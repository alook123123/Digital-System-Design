# mips_assembler_full.py
"""
Full Python MIPS Assembler + GUI (single-file)
- Two-pass assembler (labels, .org, .text/.data sections)
- Supports R/I/J types and a set of pseudo-instructions
- Directives: .text, .data, .org, .word, .half, .byte, .asciiz
- GUI (Tkinter) with:
    * Source editor
    * Start Address (default 0x00400000)
    * Endianness option (Big / Little)
    * Assemble Program, Assemble Single Instruction
    * Save Binary (.bin) and Save Hex Listing (.txt)
- Error reporting with line numbers and addresses

This is a compact educational assembler (not a production-grade assembler).
"""
import struct
import re
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext

# ---------------------------
# Registers & opcode tables
# ---------------------------
REGISTER_MAP = {
    '$zero':0, '$0':0, '$at':1,
    '$v0':2, '$v1':3,
    '$a0':4, '$a1':5, '$a2':6, '$a3':7,
    '$t0':8, '$t1':9, '$t2':10, '$t3':11, '$t4':12, '$t5':13, '$t6':14, '$t7':15,
    '$s0':16, '$s1':17, '$s2':18, '$s3':19, '$s4':20, '$s5':21, '$s6':22, '$s7':23,
    '$t8':24, '$t9':25, '$k0':26, '$k1':27, '$gp':28, '$sp':29, '$fp':30, '$ra':31
}
# numeric $n
for i in range(32):
    REGISTER_MAP[f'${i}'] = i

R_FUNCTS = {
    'add': 0x20, 'addu':0x21, 'sub':0x22, 'subu':0x23,
    'and':0x24, 'or':0x25, 'xor':0x26, 'nor':0x27,
    'slt':0x2a,
    'sll':0x00, 'srl':0x02, 'sra':0x03,
    'jr':0x08
}

I_OPCODES = {
    'addi':0x08, 'addiu':0x09, 'andi':0x0c, 'ori':0x0d, 'xori':0x0e,
    'lui':0x0f,
    'lw':0x23, 'sw':0x2b, 'lb':0x20, 'sb':0x28,
    'beq':0x04, 'bne':0x05
}

J_OPCODES = {'j':0x02, 'jal':0x03}

# pseudo-instructions mapping to expansions (implemented in assembler)
PSEUDOS = ['move','li','nop','blt','bgt','ble','bge']

# ---------------------------
# Helpers
# ---------------------------
int_re = re.compile(r"^[-+]?(0x[0-9a-fA-F]+|0b[01]+|\d+)$")

def parse_imm(s):
    s = s.strip()
    m = int_re.match(s)
    if not m:
        raise ValueError(f'Invalid immediate: {s}')
    if s.startswith(('0x','-0x','+0x')):
        return int(s,16)
    if s.startswith(('0b','-0b','+0b')):
        return int(s,2)
    return int(s,10)

def regnum(r):
    r = r.strip()
    if r in REGISTER_MAP:
        return REGISTER_MAP[r]
    raise ValueError(f'Unknown register: {r}')

def to_signed(val, bits):
    # convert unsigned val to signed int
    if val & (1 << (bits-1)):
        return val - (1<<bits)
    return val

# ---------------------------
# Instruction assembly
# ---------------------------
token_re = re.compile(r'\$?\w+\b|\(.*?\)|[-+]?(?:0x[0-9a-fA-F]+|0b[01]+|\d+)|[:,]|\S')

def tokenize(inst_text):
    # split tokens but keep parentheses as single tokens
    return [t for t in token_re.findall(inst_text) if t.strip() != ',']

def expand_pseudo(line):
    parts = line.strip()
    if not parts:
        return [line]
    # remove comments for detection
    base = re.split(r'(#|//)', parts)[0].strip()
    if not base:
        return [line]
    toks = tokenize(base)
    op = toks[0].lower()
    if op == 'move':
        # move rd, rs  -> add rd, rs, $zero
        if len(toks) >= 3:
            return [f'add {toks[1]}, {toks[2]}, $zero']
    if op == 'li':
        # li rt, imm
        if len(toks) >= 3:
            rt = toks[1]; imm = toks[2]
            try:
                val = parse_imm(imm)
            except:
                # unknown immediate, leave as-is
                return [line]
            if -32768 <= val <= 0xffff and -0x8000 <= val <= 0x7fff:
                return [f'addi {rt}, $zero, {val}']
            else:
                upper = (val >> 16) & 0xffff
                lower = val & 0xffff
                if upper != 0:
                    ins = [f'lui {rt}, {upper}']
                    if lower != 0:
                        ins.append(f'ori {rt}, {rt}, {lower}')
                    return ins
                else:
                    return [f'addi {rt}, $zero, {to_signed(lower,16)}']
    if op == 'nop':
        return ['sll $zero, $zero, 0']
    if op in ('blt','bgt','ble','bge'):
        # form op rs, rt, label
        if len(toks) >= 4:
            rs, rt, label = toks[1], toks[2], toks[3]
            if op == 'blt':
                return [f'slt $at, {rs}, {rt}', f'bne $at, $zero, {label}']
            if op == 'bgt':
                return [f'slt $at, {rt}, {rs}', f'bne $at, $zero, {label}']
            if op == 'ble':
                return [f'slt $at, {rt}, {rs}', f'beq $at, $zero, {label}']
            if op == 'bge':
                return [f'slt $at, {rs}, {rt}', f'beq $at, $zero, {label}']
    return [line]

def assemble_instruction(inst_text, pc=0, labels=None, current_section='text', lineno=None):
    """
    Assemble one instruction text into 32-bit word.
    pc: byte address of this instruction
    labels: dict mapping label->address
    """
    original = inst_text
    # strip comments
    inst_text = re.split(r'(#|//)', inst_text)[0].strip()
    if not inst_text:
        return None
    toks = tokenize(inst_text)
    if not toks:
        return None
    op = toks[0].lower()
    args = [t for t in toks[1:] if t != ',']
    # R-type
    if op in R_FUNCTS:
        funct = R_FUNCTS[op]
        opcode = 0
        shamt = 0
        rs = rt = rd = 0
        if op in ('sll','srl','sra'):
            if len(args) != 3:
                raise ValueError(f'Bad args for {op}: {args}')
            rd = regnum(args[0]); rt = regnum(args[1]); shamt = parse_imm(args[2]) & 0x1f
        elif op == 'jr':
            if len(args) != 1:
                raise ValueError('jr takes one register')
            rs = regnum(args[0])
        else:
            if len(args) != 3:
                raise ValueError(f'Bad args for {op}: {args}')
            rd = regnum(args[0]); rs = regnum(args[1]); rt = regnum(args[2])
        word = (opcode<<26) | (rs<<21) | (rt<<16) | (rd<<11) | (shamt<<6) | funct
        return word
    # I-type
    if op in I_OPCODES:
        opcode = I_OPCODES[op]
        rs = rt = imm = 0
        if op == 'lui':
            if len(args) != 2:
                raise ValueError('lui rt, imm')
            rt = regnum(args[0]); imm = parse_imm(args[1]) & 0xffff; rs = 0
        elif op in ('lw','sw','lb','sb'):
            if len(args) != 2:
                raise ValueError(f'{op} rt, offset(base)')
            rt = regnum(args[0])
            m = re.match(r'([-+]?0x[0-9a-fA-F]+|[-+]?\d+)\((\$?\w+)\)', args[1])
            if not m:
                raise ValueError('Bad memory operand; use offset(base)')
            imm = parse_imm(m.group(1)) & 0xffff
            rs = regnum(m.group(2))
        elif op in ('beq','bne'):
            if len(args) != 3:
                raise ValueError(f'{op} rs, rt, label')
            rs = regnum(args[0]); rt = regnum(args[1]); target = args[2]
            if labels is None:
                raise ValueError('Labels needed for branch assembly')
            if target in labels:
                target_addr = labels[target]
            else:
                try:
                    target_addr = parse_imm(target)
                except:
                    raise ValueError(f'Unknown label {target}')
            offset = (target_addr - (pc + 4)) // 4
            imm = offset & 0xffff
        else:
            # general I-type: rt, rs, imm
            if len(args) != 3:
                raise ValueError(f'Bad args for {op}: {args}')
            rt = regnum(args[0]); rs = regnum(args[1]); imm = parse_imm(args[2]) & 0xffff
        word = (opcode<<26) | (rs<<21) | (rt<<16) | (imm & 0xffff)
        return word
    # J-type
    if op in J_OPCODES:
        opcode = J_OPCODES[op]
        if len(args) != 1:
            raise ValueError('j target')
        target = args[0]
        if labels is None or target not in labels:
            try:
                target_addr = parse_imm(target)
            except:
                raise ValueError(f'Unknown label {target}')
        else:
            target_addr = labels[target]
        addr_field = (target_addr >> 2) & 0x03ffffff
        word = (opcode<<26) | addr_field
        return word
    raise ValueError(f'Unsupported opcode: {op} (from: "{original}")')

# ---------------------------
# Program assembly (two-pass)
# ---------------------------
def preprocess_lines(source_text):
    # returns list of original lines and a cleaned list (expanded pseudos keep comments removed for assembly)
    lines = source_text.splitlines()
    cleaned = []
    for i, ln in enumerate(lines, start=1):
        # keep original
        # remove inline comments
        ln_nocom = re.split(r'(#|//)', ln)[0]
        if ln_nocom.strip() == '':
            cleaned.append(('', i))
            continue
        # expand pseudos - may produce multiple lines
        expansions = expand_pseudo(ln_nocom)
        for e in expansions:
            cleaned.append((e.strip(), i))
    return cleaned

def assemble_program(source_text, base_addr=0x00400000):
    """
    Assemble full program text.
    Returns: list of (addr, value) and labels dict.
    """
    cleaned = preprocess_lines(source_text)  # list of (line_text, lineno)
    labels = {}
    addr = base_addr
    section = 'text'
    # First pass: build label table and allocate addresses for directives and instructions
    for text, lineno in cleaned:
        if not text:
            continue
        if text.startswith('.'):
            parts = text.split()
            dirn = parts[0]
            if dirn == '.text':
                section = 'text'; continue
            if dirn == '.data':
                section = 'data'; continue
            if dirn == '.org' and len(parts) >= 2:
                addr = parse_imm(parts[1]); continue
            if dirn == '.word':
                # may have multiple comma-separated values
                values = ' '.join(parts[1:])
                for v in [x.strip() for x in values.split(',') if x.strip()!='']:
                    labels  # no-op but keep pattern
                    addr += 4
                continue
            if dirn == '.half':
                values = ' '.join(parts[1:])
                for v in [x.strip() for x in values.split(',') if x.strip()!='']:
                    addr += 2
                continue
            if dirn == '.byte':
                values = ' '.join(parts[1:])
                for v in [x.strip() for x in values.split(',') if x.strip()!='']:
                    addr += 1
                continue
            if dirn == '.asciiz':
                # simple approximation - count bytes in literal if provided
                rest = text[len('.asciiz'):].strip()
                if rest.startswith('"') and rest.endswith('"'):
                    s = rest[1:-1]
                    addr += len(s) + 1
                continue
            continue
        # label-only line?
        if text.endswith(':'):
            name = text[:-1].strip()
            labels[name] = addr
            continue
        # label + instruction on same line?
        if ':' in text:
            lbl, rest = text.split(':', 1)
            labels[lbl.strip()] = addr
            rest = rest.strip()
            if not rest:
                continue
            text = rest
            # fall through to count size
        # assume an instruction -> 4 bytes
        addr += 4

    # Second pass: actually emit words and data with resolved labels
    addr = base_addr
    words = []  # list of (addr, value)
    for text, lineno in cleaned:
        if not text:
            continue
        if text.startswith('.'):
            parts = text.split()
            dirn = parts[0]
            if dirn == '.text':
                section = 'text'; continue
            if dirn == '.data':
                section = 'data'; continue
            if dirn == '.org' and len(parts) >= 2:
                addr = parse_imm(parts[1]); continue
            if dirn == '.word':
                values = ' '.join(parts[1:])
                for v in [x.strip() for x in values.split(',') if x.strip()!='']:
                    # v might be numeric or label
                    if int_re.match(v):
                        val = parse_imm(v)
                    else:
                        val = labels.get(v, 0)
                    words.append((addr, val & 0xffffffff)); addr += 4
                continue
            if dirn == '.half':
                values = ' '.join(parts[1:])
                for v in [x.strip() for x in values.split(',') if x.strip()!='']:
                    if int_re.match(v):
                        val = parse_imm(v)
                    else:
                        val = labels.get(v, 0)
                    # store half as 16-bit in low bits of a 32-bit word (we will pack bytes later)
                    words.append((addr, val & 0xffff)); addr += 2
                continue
            if dirn == '.byte':
                values = ' '.join(parts[1:])
                for v in [x.strip() for x in values.split(',') if x.strip()!='']:
                    if int_re.match(v):
                        val = parse_imm(v)
                    else:
                        val = labels.get(v, 0)
                    words.append((addr, val & 0xff)); addr += 1
                continue
            if dirn == '.asciiz':
                rest = text[len('.asciiz'):].strip()
                if rest.startswith('"') and rest.endswith('"'):
                    s = rest[1:-1]
                    for ch in s:
                        words.append((addr, ord(ch) & 0xff)); addr += 1
                    words.append((addr, 0)); addr += 1
                continue
            continue
        # label line
        if text.endswith(':'):
            continue
        if ':' in text:
            lbl, rest = text.split(':', 1)
            rest = rest.strip()
            if not rest:
                continue
            text = rest
        # assemble instruction
        try:
            w = assemble_instruction(text, pc=addr, labels=labels, current_section=section, lineno=lineno)
        except Exception as e:
            raise RuntimeError(f'Error at line {lineno} (addr 0x{addr:08x}) assembling "{text}": {e}')
        if w is None:
            continue
        words.append((addr, w & 0xffffffff))
        addr += 4

    return words, labels

# ---------------------------
# Convert words list to contiguous bytes (respecting sizes for .byte/.half)
# ---------------------------
def words_to_bytes(words, default_start=None, endianness='big'):
    """
    words: list of (addr, value). Values may be 32-bit, 16-bit, or 8-bit depending on allocation.
    We'll pack bytes from min address to max address inclusive. Gaps filled with zeros.
    endianness: 'big' or 'little'
    """
    if not words:
        return b''
    words_sorted = sorted(words, key=lambda x: x[0])
    start = words_sorted[0][0] if default_start is None else default_start
    end = max(a for a,_ in words_sorted) + 1  # +1 because there may be bytes
    # Determine end by considering that 32-bit words occupy 4 bytes aligned: but we stored individual bytes at their own addresses
    # We'll find highest address key
    max_addr = max(a for a,_ in words_sorted)
    # For 32-bit words at aligned addresses we need +4; for halves +2 and bytes +1. We stored all entries individually (words for instructions + words for .word)
    # If we find addresses that match 4-byte aligned and have 32-bit values, ensure up to addr+4
    end_candidate = max_addr + 1
    for a,v in words_sorted:
        # heuristics: if v fits >0xffff maybe it's 32-bit
        if a % 4 == 0 and (v > 0xff or v & 0xffff0000):
            end_candidate = max(end_candidate, a + 4)
        elif a % 2 == 0 and v > 0xff:
            end_candidate = max(end_candidate, a + 2)
        else:
            end_candidate = max(end_candidate, a + 1)
    end = end_candidate
    size = end - start
    buf = bytearray(size)
    for a,v in words_sorted:
        offset = a - start
        # place value size-based:
        # If address aligned to 4 and v uses >8 bits, assume 4-byte word
        if offset < 0:
            # skip values before start
            continue
        if a % 4 == 0 and v > 0xff:
            # 4 bytes
            b = struct.pack('>I', v & 0xffffffff)
            if endianness == 'little':
                b = b[::-1]
            buf[offset:offset+4] = b
        elif a % 2 == 0 and v > 0xff:
            # half (2 bytes)
            b = struct.pack('>H', v & 0xffff)
            if endianness == 'little':
                b = b[::-1]
            buf[offset:offset+2] = b
        else:
            # byte
            buf[offset] = v & 0xff
    return bytes(buf), start

def word_to_hex(w):
    return f'{w:08x}'

def word_to_bin(w):
    return f'{w:032b}'

# ---------------------------
# GUI
# ---------------------------
class AssemblerGUI:
    def __init__(self, master):
        self.master = master
        master.title('MIPS Assembler - Full')
        # layout frames
        top = tk.Frame(master)
        top.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)

        left = tk.Frame(top)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        right = tk.Frame(top)
        right.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        # Source editor
        tk.Label(left, text='MIPS Source:').pack(anchor='w')
        self.src = scrolledtext.ScrolledText(left, width=70, height=30, font=('Consolas',10))
        self.src.pack(fill=tk.BOTH, expand=True)
        sample = """# Sample program
.text
main:
    addi $t0, $zero, 5
    addi $t1, $zero, 10
    add $t2, $t0, $t1
    sw $t2, 0($sp)
    j end

.data
msg:
    .asciiz "Hello"
val:
    .word 0x12345678
end:
"""
        self.src.insert('1.0', sample)

        btn_frame = tk.Frame(left)
        btn_frame.pack(fill=tk.X, pady=4)
        tk.Button(btn_frame, text='Assemble Program', command=self.assemble_program).pack(side=tk.LEFT)
        tk.Button(btn_frame, text='Assemble Single Instruction', command=self.assemble_single_prompt).pack(side=tk.LEFT)
        tk.Button(btn_frame, text='Clear Output', command=self.clear_output).pack(side=tk.LEFT)

        # Options panel
        opt_frame = tk.Frame(right)
        opt_frame.pack(fill=tk.X)
        tk.Label(opt_frame, text='Start Address (hex):').grid(row=0, column=0, sticky='w')
        self.start_entry = tk.Entry(opt_frame, width=14)
        self.start_entry.grid(row=0, column=1, sticky='w')
        self.start_entry.insert(0, '0x00400000')
        tk.Label(opt_frame, text='Endianness:').grid(row=1, column=0, sticky='w')
        self.endian_var = tk.StringVar(value='big')
        tk.OptionMenu(opt_frame, self.endian_var, 'big', 'little').grid(row=1, column=1, sticky='w')

        # Output area
        tk.Label(right, text='Output (Hex / Binary / Errors):').pack(anchor='w')
        self.out = scrolledtext.ScrolledText(right, width=70, height=20, font=('Consolas',10))
        self.out.pack(fill=tk.BOTH, expand=True)

        save_frame = tk.Frame(right)
        save_frame.pack(fill=tk.X, pady=4)
        tk.Button(save_frame, text='Save Binary (.bin)', command=self.save_binary).pack(side=tk.LEFT)
        tk.Button(save_frame, text='Save Hex Listing (.txt)', command=self.save_hex).pack(side=tk.LEFT)

        # status bar
        self.status = tk.StringVar(value='Ready')
        tk.Label(master, textvariable=self.status, anchor='w').pack(fill=tk.X)

        self.last_words = None
        self.base_addr = 0x00400000

    def set_status(self, s):
        self.status.set(s)

    def clear_output(self):
        self.out.delete('1.0', tk.END)

    def assemble_program(self):
        src = self.src.get('1.0', tk.END)
        # parse start address
        try:
            start_text = self.start_entry.get().strip()
            base_addr = parse_imm(start_text) if start_text else 0x00400000
        except Exception as e:
            messagebox.showerror('Address error', f'Bad start address: {e}')
            return
        try:
            words, labels = assemble_program(src, base_addr=base_addr)
        except Exception as e:
            messagebox.showerror('Assemble error', str(e))
            self.set_status('Assemble failed')
            return
        if not words:
            self.out.insert(tk.END, 'No output words\n')
            self.set_status('Nothing assembled')
            return
        # print listing
        s = []
        for addr,w in words:
            if isinstance(w, int) and (addr % 4 == 0) and (w > 0xff):
                s.append(f'0x{addr:08x}: {word_to_hex(w)}\t{word_to_bin(w)}')
            else:
                # small-sized data
                s.append(f'0x{addr:08x}: {w:#x}')
        self.out.delete('1.0', tk.END)
        self.out.insert('1.0', '\n'.join(s))
        self.last_words = words
        self.base_addr = base_addr
        self.set_status(f'Assembled {len(words)} entries (start 0x{base_addr:08x})')

    def assemble_single_prompt(self):
        def do():
            instr = entry.get().strip()
            win.destroy()
            if not instr:
                return
            try:
                # allow using default labels empty
                w = assemble_instruction(instr, pc=0, labels={}, current_section='text')
            except Exception as e:
                messagebox.showerror('Error', str(e))
                return
            txt = f'{instr}\nhex: 0x{word_to_hex(w)}\nbin: {word_to_bin(w)}\n'
            self.out.insert(tk.END, txt + '\n')
            self.set_status('Assembled single instruction')
        win = tk.Toplevel(self.master)
        win.title('Assemble Single Instruction')
        tk.Label(win, text='Instruction:').pack(anchor='w')
        entry = tk.Entry(win, width=80)
        entry.pack(fill=tk.X)
        entry.focus()
        tk.Button(win, text='Assemble', command=do).pack()

    def save_binary(self):
        if not self.last_words:
            messagebox.showinfo('No data', 'No assembled binary to save. Assemble program first.')
            return
        fname = filedialog.asksaveasfilename(defaultextension='.bin', filetypes=[('Binary','*.bin'),('All','*.*')])
        if not fname:
            return
        endianness = self.endian_var.get()
        try:
            b, start = words_to_bytes(self.last_words, default_start=self.base_addr, endianness=endianness)
        except Exception as e:
            messagebox.showerror('Error', f'Failed to produce binary: {e}')
            return
        with open(fname, 'wb') as f:
            f.write(b)
        self.set_status(f'Wrote {len(b)} bytes to {fname} (start 0x{start:08x})')

    def save_hex(self):
        if not self.last_words:
            messagebox.showinfo('No data', 'No assembled data. Assemble program first.')
            return
        fname = filedialog.asksaveasfilename(defaultextension='.txt', filetypes=[('Text','*.txt'),('All','*.*')])
        if not fname:
            return
        with open(fname, 'w') as f:
            for addr,w in self.last_words:
                if isinstance(w, int) and (addr % 4 == 0) and (w > 0xff):
                    f.write(f'0x{addr:08x}: {word_to_hex(w)}\n')
                else:
                    f.write(f'0x{addr:08x}: {w:#x}\n')
        self.set_status(f'Wrote hex listing to {fname}')

# ---------------------------
# Run
# ---------------------------
def main():
    root = tk.Tk()
    app = AssemblerGUI(root)
    root.mainloop()

if __name__ == '__main__':
    main()
