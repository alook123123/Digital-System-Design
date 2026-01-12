module project(CLOCK_50,SW,LEDG,LEDR,HEX0,HEX1,HEX2,HEX3,HEX4,HEX5,HEX6,HEX7); 
	input CLOCK_50;
	input	[17:0] SW;
	output	[17:0] LEDR;
	output	[7:0] LEDG;
	
	output [0:6] HEX0,HEX1,HEX2,HEX3,HEX4,HEX5,HEX6,HEX7;
	reg [31:0] w_hex;
	wire [31:0] result_out, instr_out;
	assign LEDG[7] = Stall; 
	
	
	mips_pipeline CPU(
						.clk(SW[17]),
						.reset(SW[16]),
						.Stall(Stall),
						.instr_out(instr_out),
						.pc_out_check(LEDR[17:0]),
						.forwardA_out(LEDG[1:0]),
						.forwardB_out(LEDG[3:2]),
						.result_out(result_out)
						);
	
	always @(*) begin
			case (SW[0])
				1'b0: w_hex = instr_out;   
				1'b1: w_hex = result_out;
				default: w_hex = 32'b0;
			endcase
		end
		
	HEX_7SEG_DECODE H0(.BIN(w_hex[3:0]), .SSD(HEX0));
	HEX_7SEG_DECODE H1(.BIN(w_hex[7:4]), .SSD(HEX1));
	HEX_7SEG_DECODE H2(.BIN(w_hex[11:8]), .SSD(HEX2));
	HEX_7SEG_DECODE H3(.BIN(w_hex[15:12]), .SSD(HEX3));
	HEX_7SEG_DECODE H4(.BIN(w_hex[19:16]), .SSD(HEX4));
	HEX_7SEG_DECODE H5(.BIN(w_hex[23:20]), .SSD(HEX5));
	HEX_7SEG_DECODE H6(.BIN(w_hex[27:24]), .SSD(HEX6));
	HEX_7SEG_DECODE H7(.BIN(w_hex[31:28]), .SSD(HEX7));
	

endmodule


module mips_pipeline(
	input clk, 
	input reset, 
	output Stall,
	output [31:0] instr_out, 
	output [17:0] pc_out_check, 
	output [1:0] forwardA_out,
	output [1:0] forwardB_out,
	output [31:0] result_out
);

	assign result_out = WB_data;
	assign forwardA_out = ForwardA;
	assign forwardB_out = ForwardB;
	
	wire Flush;
	assign Flush = Jump || (EXMEM_Branch && EXMEM_Zero);
	assign pc_out_check = PC;
	assign instr_out = IFID_instr;
	wire [1:0] ForwardA, ForwardB;
	wire [31:0] ALU_A, ALU_B_pre;
	assign ALU_A =
    (ForwardA == 2'b00) ? IDEX_RD1 :
    (ForwardA == 2'b10) ? EXMEM_ALU :
    (ForwardA == 2'b01) ? WB_data :
    IDEX_RD1;

	assign ALU_B_pre =
    (ForwardB == 2'b00) ? IDEX_RD2 :
    (ForwardB == 2'b10) ? EXMEM_ALU :
    (ForwardB == 2'b01) ? WB_data :
    IDEX_RD2;
    
    wire [31:0] PC;
	wire [31:0] PC_plus4, PC_next, PC_write;
	wire [31:0] instr;
	assign PC_plus4 = PC + 4;
	assign PC_write = Stall ? PC : PC_next;
	
	wire [5:0] opcode = IFID_instr[31:26];
    wire [4:0] rs = IFID_instr[25:21];
    wire [4:0] rt = IFID_instr[20:16];
    wire [4:0] rd = IFID_instr[15:11];
    wire [15:0] imm = IFID_instr[15:0];

    wire RegDst, ALUSrc, MemRead, MemWrite, MemtoReg, RegWrite, Branch;
    wire [2:0] ALUop;
    
    wire [31:0] RD1, RD2;
    wire [31:0] WB_data;
    
    wire [4:0] EX_WriteReg = IDEX_RegDst ? IDEX_rd : IDEX_rt;
    wire [31:0] ALU_B = IDEX_ALUSrc ? IDEX_Imm : ALU_B_pre;
    wire [31:0] ALU_out;
    wire Zero;
    
    wire [31:0] SignExtImm = {{16{imm[15]}}, imm};
    wire Jump;
    wire [31:0] JumpAddr;

    /* ===================== IF ===================== */
	Program_Counter PCU(
		.clk(clk),
		.reset(reset),
		.PC_in(PC_write),
		.PC_out(PC)
	);

	/* Instruction Memory */
	Instruction_Memory IM(
    .read_address(PC[31:2]),
    .instruction(instr),
    .reset(reset));
    
	/* IF/ID */
    reg [31:0] IFID_PC4, IFID_instr;
	always @(posedge clk or posedge reset) begin
    if (reset) begin
        IFID_instr <= 32'b0;
        IFID_PC4   <= 32'b0;
    end
    else if (Flush) begin
        IFID_instr <= 32'b0; 
        IFID_PC4   <= 32'b0;
    end
    else if (!Stall) begin
        IFID_instr <= instr;
        IFID_PC4   <= PC_plus4;
		end
	end
	
    /* ===================== ID ===================== */
    control CU(
    opcode,
    RegDst, Branch, MemRead, MemtoReg,
    ALUop, MemWrite, ALUsrc, RegWrite, Jump
    );

    Register_File RF(
        clk, rs, rt,
        MEMWB_rd, RD1, RD2,
        WB_data, MEMWB_RegWrite
    );
    
    assign JumpAddr = { IFID_PC4[31:28], IFID_instr[25:0], 2'b00 };
    /* ID/EX */
    reg [31:0] IDEX_RD1, IDEX_RD2, IDEX_Imm, IDEX_PC4;
    reg [4:0] IDEX_rs, IDEX_rt, IDEX_rd;
    reg IDEX_RegDst, IDEX_ALUSrc, IDEX_MemRead,
        IDEX_MemWrite, IDEX_MemtoReg, IDEX_RegWrite, IDEX_Branch;
    reg [2:0] IDEX_ALUop;
    always @(posedge clk or posedge reset) begin
    if (reset) begin
        IDEX_RegDst   <= 0;
        IDEX_ALUSrc   <= 0;
        IDEX_MemRead  <= 0;
        IDEX_MemWrite <= 0;
        IDEX_MemtoReg <= 0;
        IDEX_RegWrite <= 0;
        IDEX_Branch   <= 0;
        IDEX_ALUop    <= 0;

        IDEX_RD1 <= 0;
        IDEX_RD2 <= 0;
        IDEX_Imm <= 0;
        IDEX_PC4 <= 0;
        IDEX_rs  <= 0;
        IDEX_rt  <= 0;
        IDEX_rd  <= 0;
    end
    else if (Stall) begin
        IDEX_RegDst   <= 0;
        IDEX_ALUSrc   <= 0;
        IDEX_MemRead  <= 0;
        IDEX_MemWrite <= 0;
        IDEX_MemtoReg <= 0;
        IDEX_RegWrite <= 0;
        IDEX_Branch   <= 0;
        IDEX_ALUop    <= 0;
    end
    else begin
        IDEX_RD1 <= RD1;
        IDEX_RD2 <= RD2;
        IDEX_Imm <= SignExtImm;
        IDEX_PC4 <= IFID_PC4;
        IDEX_rs  <= rs;
        IDEX_rt  <= rt;
        IDEX_rd  <= rd;

        IDEX_RegDst   <= RegDst;
        IDEX_ALUSrc   <= ALUsrc;
        IDEX_MemRead  <= MemRead;
        IDEX_MemWrite <= MemWrite;
        IDEX_MemtoReg <= MemtoReg;
        IDEX_RegWrite <= RegWrite;
        IDEX_Branch   <= Branch;
        IDEX_ALUop    <= ALUop;
		end
	end


    /* ===================== EX ===================== */

    alu ALU(
    IDEX_ALUop,
    ALU_A,
    ALU_B,
    ALU_out,
    Zero);

	ForwardingUnit FU(
    EXMEM_RegWrite,
    MEMWB_RegWrite,
    EXMEM_rd,
    MEMWB_rd,
    IDEX_rs,
    IDEX_rt,
    ForwardA,
    ForwardB
    );
    
    wire [31:0] BranchTarget = IDEX_PC4 + (IDEX_Imm << 2);

    /* EX/MEM */
    wire [31:0] StoreData;

	assign StoreData = (ForwardB == 2'b10) ? EXMEM_ALU : (ForwardB == 2'b01) ? WB_data :IDEX_RD2;
	
    reg [31:0] EXMEM_ALU, EXMEM_RD2, EXMEM_BranchTarget;
    reg [4:0]  EXMEM_rd;
    reg EXMEM_MemRead, EXMEM_MemWrite,
        EXMEM_MemtoReg, EXMEM_RegWrite, EXMEM_Branch;
    reg EXMEM_Zero;

    always @(posedge clk) begin
        EXMEM_ALU <= ALU_out;
        EXMEM_RD2 <= StoreData;
        EXMEM_rd  <= EX_WriteReg;
        EXMEM_Zero <= Zero;
        EXMEM_BranchTarget <= BranchTarget;

        EXMEM_MemRead  <= IDEX_MemRead;
        EXMEM_MemWrite <= IDEX_MemWrite;
        EXMEM_MemtoReg <= IDEX_MemtoReg;
        EXMEM_RegWrite <= IDEX_RegWrite;
        EXMEM_Branch   <= IDEX_Branch;
    end

    /* ===================== MEM ===================== */
    wire [31:0] MemData;

    Data_Memory DM(
        EXMEM_ALU[31:2],
        EXMEM_RD2,
        MemData,
        EXMEM_MemRead,
        EXMEM_MemWrite
    );

    assign PC_next =
    Jump ? JumpAddr :
    (EXMEM_Branch & EXMEM_Zero) ? EXMEM_BranchTarget :
    PC_plus4;
    
    

    /* MEM/WB */
    reg [31:0] MEMWB_Mem, MEMWB_ALU;
    reg [4:0]  MEMWB_rd;
    reg MEMWB_MemtoReg, MEMWB_RegWrite;

    always @(posedge clk) begin
        MEMWB_Mem <= MemData;
        MEMWB_ALU <= EXMEM_ALU;
        MEMWB_rd  <= EXMEM_rd;
        MEMWB_MemtoReg <= EXMEM_MemtoReg;
        MEMWB_RegWrite <= EXMEM_RegWrite;
    end

    assign WB_data =
        MEMWB_MemtoReg ? MEMWB_Mem : MEMWB_ALU;


HazardDetectionUnit HDU(
    IDEX_MemRead,
    IDEX_rt,
    IFID_instr[25:21],
    IFID_instr[20:16],
    reset,        
    Stall
);
endmodule





module HEX_7SEG_DECODE(BIN, SSD);
  input [3:0] BIN;
  output reg [0:6] SSD;
  always begin
    case(BIN)
      0:SSD=7'b0000001;
      1:SSD=7'b1001111;
      2:SSD=7'b0010010;
      3:SSD=7'b0000110;
      4:SSD=7'b1001100;
      5:SSD=7'b0100100;
      6:SSD=7'b0100000;
      7:SSD=7'b0001111;
      8:SSD=7'b0000000;
      9:SSD=7'b0001100;
      10:SSD=7'b0001000;
      11:SSD=7'b1100000;
      12:SSD=7'b0110001;
      13:SSD=7'b1000010;
      14:SSD=7'b0110000;
      15:SSD=7'b0111000;
    endcase
  end
endmodule

module Program_Counter (clk, reset, PC_in, PC_out);
	input clk, reset;
	input [31:0] PC_in;
	output reg [31:0] PC_out;
	always @ (posedge clk or posedge reset)
	begin
		if(reset==1'b1)
			PC_out<=0;
		else
			PC_out<=PC_in;
	end
endmodule

module Adder32Bit(input1, input2, out);
    input [31:0] input1, input2;
    output [31:0] out;
    reg [31:0]out;
    always@( input1 or input2)
        begin
            out <= input1 + input2;
        end
endmodule

module alu(
	input [2:0] alufn,
	input [31:0] ra,
	input [31:0] rb_or_imm,
	output reg [31:0] aluout,
	output reg zero);
	parameter	ALU_OP_ADD	    = 3'b000,
			    ALU_OP_SUB	    = 3'b001,
			    ALU_OP_AND	    = 3'b010,
			    ALU_OP_OR		= 3'b011,
			    ALU_OP_XOR	    = 3'b100,
			    ALU_OP_LW		= 3'b101,
			    ALU_OP_SW		= 3'b110,
			    ALU_OP_BEQ	    = 3'b111;

always @(*) begin
    aluout = 0;
    zero = (ra == rb_or_imm);
    case(alufn)
        3'b000: aluout = ra + rb_or_imm;
        3'b001: aluout = ra - rb_or_imm;
        3'b010: aluout = ra & rb_or_imm;
        3'b011: aluout = ra | rb_or_imm;
    endcase
end
endmodule

module Register_File (
    clk,
    read_addr_1,
    read_addr_2,
    write_addr,
    read_data_1,
    read_data_2,
    write_data,
    RegWrite
);
    input clk;
    input RegWrite;
    input [4:0] read_addr_1, read_addr_2, write_addr;
    input [31:0] write_data;

    output [31:0] read_data_1, read_data_2;

    reg [31:0] Regfile [31:0];
    integer k;

    // ================= INIT =================
    initial begin
        for (k = 0; k < 32; k = k + 1)
            Regfile[k] = 32'b0;
    end

    // ================= READ (COMBINATIONAL) =================
    assign read_data_1 = (read_addr_1 == 0) ? 32'b0 : Regfile[read_addr_1];
    assign read_data_2 = (read_addr_2 == 0) ? 32'b0 : Regfile[read_addr_2];

    // ================= WRITE (SEQUENTIAL) =================
    always @(posedge clk) begin
        if (RegWrite && (write_addr != 0))
            Regfile[write_addr] <= write_data;
    end

endmodule


module Data_Memory (addr, write_data, read_data, MemRead, MemWrite);
	input [31:0] addr;
	input [31:0] write_data;
	output [31:0] read_data;
	input MemRead, MemWrite;
	reg [31:0] DMemory [255:0];
	integer k;
	assign read_data = (MemRead) ? DMemory[addr] : 32'bx;
	initial begin
		for (k=0; k<64; k=k+1) 
            begin
		           DMemory[k] = 32'b0;
			end
		DMemory[11] = 99;
	end
	always @(*)
	begin
		if (MemWrite) DMemory[addr] = write_data;
	end
endmodule

module Sign_Extension (sign_in, sign_out);
	input [15:0] sign_in;
	output [31:0] sign_out;
	assign sign_out[15:0]=sign_in[15:0];
	assign sign_out[31:16]=sign_in[15]?16'b1111_1111_1111_1111:16'b0;
endmodule

module Mux_32_bit (in0, in1, mux_out, select);
	parameter N = 32;
	input [N-1:0] in0, in1;
	output [N-1:0] mux_out;
	input select;
	assign mux_out = select? in1: in0 ;
endmodule

module Mux_5_bit (in0, in1, mux_out, select);
	parameter N = 5;
	input [N-1:0] in0, in1;
	output [N-1:0] mux_out;
	input select;
	assign mux_out = select? in1: in0 ;
endmodule

module Instruction_Memory (read_address, instruction, reset);
    input reset;
    input [31:0] read_address;
    output [31:0] instruction;

    reg [31:0] Imemory [63:0];
    integer k;

    // word-addressed memory
    assign instruction = Imemory[read_address];

    always @(posedge reset) begin
        // clear memory
        for (k = 0; k < 64; k = k + 1)
            Imemory[k] = 32'b0;

        // ===============================
        // I-TYPE (addi)
        // ===============================

        // addi $s0, $zero, 5
        Imemory[0] = 32'b001000_00000_10000_0000000000000101;

        // addi $s1, $zero, 10
        Imemory[1] = 32'b001000_00000_10001_0000000000001010;

        // ===============================
        // R-TYPE (add, sub, and, or)
        // ===============================

        // add  $s2, $s0, $s1   ; 5 + 10 = 15
        Imemory[2] = 32'b000000_10000_10001_10010_00000_100000;

        // sub  $s3, $s1, $s0   ; 10 - 5 = 5
        Imemory[3] = 32'b000000_10001_10000_10011_00000_100010;

        // and  $s4, $s0, $s1
        Imemory[4] = 32'b000000_10000_10001_10100_00000_100100;

        // or   $s5, $s0, $s1
        Imemory[5] = 32'b000000_10000_10001_10101_00000_100101;

        // ===============================
        // MEMORY (sw / lw)
        // ===============================

        // sw $s2, 0($zero)
        Imemory[6] = 32'b101011_00000_10010_0000000000000000;

        // lw $s3, 0($zero)    ; load-use hazard
        Imemory[7] = 32'b100011_00000_10011_0000000000000000;

        // add $s4, $s3, $s0   ; needs forwarding or stall
        Imemory[8] = 32'b000000_10011_10000_10100_00000_100000;

        // ===============================
        // BRANCH (beq)
        // ===============================

        // beq $s4, $s2, +2
        Imemory[9] = 32'b000100_10100_10010_0000000000000010;

        // addi $s0, $zero, 99   ; skipped if branch taken
        Imemory[10] = 32'b001000_00000_10000_0000000001100011;

        // addi $s1, $zero, 77   ; skipped if branch taken
        Imemory[11] = 32'b001000_00000_10001_0000000001001101;

        // ===============================
        // JUMP
        // ===============================

        // j 15
        Imemory[12] = 32'b000010_000000000000000000001111;

        // addi $s2, $zero, 123  ; skipped by jump
        Imemory[13] = 32'b001000_00000_10010_0000000001111011;

        // ===============================
        // TARGET OF JUMP
        // ===============================

        // addi $s3, $zero, 55
        Imemory[15] = 32'b001000_00000_10011_0000000000110111;

        // NOPs
        Imemory[16] = 32'b0;
        Imemory[17] = 32'b0;
    end
endmodule


module Sign_Extension_26 (sign_in, sign_out);
	input [25:0] sign_in;
	output [31:0] sign_out;
	assign sign_out[25:0]=sign_in[25:0];
	assign sign_out[31:26]=sign_in[25]?6'b111111:6'b0;
endmodule

module control(
    input  [5:0] op_code,
    output reg RegDst,
    output reg Branch,
    output reg MemRead,
    output reg MemtoReg,
    output reg [2:0] ALUop,
    output reg MemWrite,
    output reg ALUsrc,
    output reg RegWrite,
    output reg Jump
);

always @(*) begin
    RegDst = 0; Branch = 0; MemRead = 0; MemtoReg = 0;
    ALUop = 3'b000; MemWrite = 0; ALUsrc = 0; RegWrite = 0; Jump = 0;

    case(op_code)

    6'b000000: begin // R-type
    RegDst = 1;
    RegWrite = 1;
    ALUop = 3'b000;
    Jump = 0;   
end

    6'b001000: begin // addi
        ALUsrc = 1;
        RegWrite = 1;
        ALUop = 3'b000;
    end

    6'b100011: begin // lw
        ALUsrc = 1;
        MemRead = 1;
        MemtoReg = 1;
        RegWrite = 1;
        ALUop = 3'b000;
    end

    6'b101011: begin // sw
        ALUsrc = 1;
        MemWrite = 1;
        ALUop = 3'b000;
    end

    6'b000100: begin // beq
        Branch = 1;
        ALUop = 3'b001;
    end

    6'b000010: begin // j
        Jump = 1;
    end

    endcase
end
endmodule

module ForwardingUnit(
    input  EXMEM_RegWrite,
    input  MEMWB_RegWrite,
    input  [4:0] EXMEM_rd,
    input  [4:0] MEMWB_rd,
    input  [4:0] IDEX_rs,
    input  [4:0] IDEX_rt,
    output reg [1:0] ForwardA,
    output reg [1:0] ForwardB
);

always @(*) begin
    ForwardA = 2'b00;
    ForwardB = 2'b00;

    // EX hazard
    if (EXMEM_RegWrite && (EXMEM_rd != 0) && (EXMEM_rd == IDEX_rs))
        ForwardA = 2'b10;

    if (EXMEM_RegWrite && (EXMEM_rd != 0) && (EXMEM_rd == IDEX_rt))
        ForwardB = 2'b10;

    // MEM hazard
    if (MEMWB_RegWrite && (MEMWB_rd != 0) &&
        !(EXMEM_RegWrite && (EXMEM_rd != 0) && (EXMEM_rd == IDEX_rs)) &&
        (MEMWB_rd == IDEX_rs))
        ForwardA = 2'b01;

    if (MEMWB_RegWrite && (MEMWB_rd != 0) &&
        !(EXMEM_RegWrite && (EXMEM_rd != 0) && (EXMEM_rd == IDEX_rt)) &&
        (MEMWB_rd == IDEX_rt))
        ForwardB = 2'b01;
end
endmodule

module HazardDetectionUnit(
    input  IDEX_MemRead,
    input  [4:0] IDEX_rt,
    input  [4:0] IFID_rs,
    input  [4:0] IFID_rt,
    input  reset,         
    output reg Stall
);

always @(*) begin
    if (reset)
        Stall = 1'b0;
    else if (IDEX_MemRead &&
            ((IDEX_rt == IFID_rs) || (IDEX_rt == IFID_rt)) &&
            (IDEX_rt != 0))
        Stall = 1'b1;
    else
        Stall = 1'b0;
end

endmodule

