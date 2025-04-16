`timescale 1ns / 1ns    // `timescale 1ns/1ps

module TestBench ();
	logic clk, reset, MemWrite;
	logic [31:0] WriteData, DataAdr;

	// instantiates device under test (top level module)
	Top dut (
		clk,
		reset,
		MemWrite,
		WriteData,
		DataAdr
	);
	
	// initializes test
	initial begin
		reset <= 1;
		#22;		// 2.2 cycles
		reset <= 0;
	end

	// generates clock
	initial begin
	        clk <= 1;
	        forever #5 clk = ~clk;		// 5ns high + 5ns low = 10ns → 100MHz
	end

	// checks results
	always @(negedge clk) begin
		if (MemWrite) begin
			if (DataAdr === 100 & WriteData === 25) begin
				$display("Simulation succeeded");
				// $stop;
			end else if (DataAdr !== 96) begin
				$display("Simulation failed");
				// $stop;
			end
		end
	end
	
	initial begin
		$dumpfile("waveform_p.vcd");		// indicates file.vcd (Value Change Dump)
		$dumpvars(0, dut);		// dump signals from the module

		#500;
		// $dumpon;
		// $dumpoff;
		$finish;
	end
endmodule

// top level module
module Top (
		input logic clk, reset,
		output logic MemWriteM,
		output logic [31:0] WriteDataM, DataAdrM
);

	logic [31:0] PCF, InstrF, ReadDataM;
	
	// instantiate processor and memories
	Processor riscvpipelined (
		clk,
		reset,
		InstrF,
		ReadDataM,
		MemWriteM,
		PCF,
		DataAdrM, 
		WriteDataM
	);

	InstructionMemory instMemory (
		PCF,
		InstrF
	);
	DataMemory dataMemory (
		clk,
		MemWriteM,
		DataAdrM,
		WriteDataM,
		ReadDataM
	);
endmodule

module Processor (
		input logic clk, reset,
		input logic [31:0] InstrF,
		ReadDataM,
		output logic MemWriteM,
		output logic [31:0] PCF,
		ALUResultM,		// data_address
		WriteDataM
);

	logic funct7b5D, ZeroE, PCSrcE, ALUSrcE, ResultSrcEb0, RegWriteM, RegWriteW;
	logic [1:0] ImmSrcD, ResultSrcW;
	logic [2:0] funct3D, ALUControlE;
	logic [6:0] opD;

	logic StallF, StallD, FlushD, FlushE;
	logic [1:0] ForwardAE, ForwardBE;

	logic [4:0] Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW;
	
	Controller controller (
		clk, reset,
		opD, funct3D, funct7b5D, ImmSrcD,
		FlushE, ZeroE, PCSrcE, ALUControlE, ALUSrcE, ResultSrcEb0,
		MemWriteM, RegWriteM, 
		RegWriteW, ResultSrcW
	);

	Datapath datapath (
		clk, reset,
		StallF, PCF, InstrF,
		opD, funct3D, funct7b5D, StallD, FlushD, ImmSrcD,
		FlushE, ForwardAE, ForwardBE, PCSrcE, ALUControlE, ALUSrcE, ZeroE,
		MemWriteM, WriteDataM, ALUResultM, ReadDataM,
		RegWriteW, ResultSrcW,
		Rs1D, Rs2D, Rs1E, Rs2E, RdE, RdM, RdW
	);
endmodule

module Controller (
		input logic clk, reset,
		// Decode stage control signals
		input logic [6:0]  opD,
		input logic [2:0]  funct3D,
		input logic funct7b5D,
		output logic [1:0] ImmSrcD,
		// Execute stage control signals
		input logic FlushE, 
		input logic ZeroE, 
		output logic PCSrcE,		// for datapath and Hazard Unit
		output logic [2:0] ALUControlE, 
		output logic ALUSrcE,
		output logic ResultSrcEb0,		// for Hazard Unit
		// Memory stage control signals
		output logic MemWriteM,
		output logic RegWriteM,		// for Hazard Unit				  
		// Writeback stage control signals
		output logic RegWriteW,		// for datapath and Hazard Unit
		output logic [1:0] ResultSrcW
);

	// pipelined control signals
	logic RegWriteD, RegWriteE;
	logic [1:0] ResultSrcD, ResultSrcE, ResultSrcM;
	logic MemWriteD, MemWriteE;
	logic JumpD, JumpE;
	logic BranchD, BranchE;
	logic [1:0] ALUOpD;
	logic [2:0] ALUControlD;
	logic ALUSrcD;
	
	// Decode stage logic
	maindec md (
		opD, ResultSrcD, MemWriteD, BranchD,
		ALUSrcD, RegWriteD, JumpD, ImmSrcD, ALUOpD
	);
	aludec ad (
		opD[5], funct3D, funct7b5D, ALUOpD, ALUControlD
	);
	
	// Execute stage pipeline control register and logic
	floprc #(10) controlregE (
		clk, reset, FlushE,
		{RegWriteD, ResultSrcD, MemWriteD, JumpD, BranchD, ALUControlD, ALUSrcD},
		{RegWriteE, ResultSrcE, MemWriteE, JumpE, BranchE, ALUControlE, ALUSrcE}
	);

	assign PCSrcE = (BranchE & ZeroE) | JumpE;
	assign ResultSrcEb0 = ResultSrcE[0];
	
	// Memory stage pipeline control register
	flopr #(4) controlregM (
		clk, reset,
		{RegWriteE, ResultSrcE, MemWriteE},
		{RegWriteM, ResultSrcM, MemWriteM}
	);

	// Writeback stage pipeline control register
	flopr #(3) controlregW (
		clk, reset,
		{RegWriteM, ResultSrcM},
		{RegWriteW, ResultSrcW}
	);     
endmodule

module maindec (
		input  logic [6:0] op,
		output logic [1:0] ResultSrc,
		output logic MemWrite,
		output logic Branch, ALUSrc,
		output logic RegWrite, Jump,
		output logic [1:0] ImmSrc,
		output logic [1:0] ALUOp
);

	logic [10:0] controls;

	assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
					ResultSrc, Branch, ALUOp, Jump} = controls;

	always_comb
		case(op)
		// RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
			7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
			7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
			7'b0110011: controls = 11'b1_xx_0_0_00_0_10_0; // R-type 
			7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // beq
			7'b0010011: controls = 11'b1_00_1_0_00_0_10_0; // I-type ALU
			7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // jal
			7'b0000000: controls = 11'b0_00_0_0_00_0_00_0; // need valid values at reset
			default:    controls = 11'bx_xx_x_x_xx_x_xx_x; // non-implemented instruction
		endcase
endmodule

module aludec (
		input logic opb5,
		input logic [2:0] funct3,
		input logic funct7b5, 
		input logic [1:0] ALUOp,
		output logic [2:0] ALUControl
);

	logic  RtypeSub;
	assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

	always_comb
		case(ALUOp)
			2'b00:                ALUControl = 3'b000; // addition
			2'b01:                ALUControl = 3'b001; // subtraction
			default: case(funct3) // R-type or I-type ALU
								 3'b000:  if (RtypeSub) 
														ALUControl = 3'b001; // sub
													else          
														ALUControl = 3'b000; // add, addi
								 3'b010:    ALUControl = 3'b101; // slt, slti
								 3'b110:    ALUControl = 3'b011; // or, ori
								 3'b111:    ALUControl = 3'b010; // and, andi
								 default:   ALUControl = 3'bxxx; // ???
							 endcase
		endcase
endmodule

module Datapath (
		input logic clk, reset,
		// Fetch stage signals
		input logic StallF,
		output logic [31:0] PCF,
		input logic [31:0] InstrF,
		// Decode stage signals
		output logic [6:0] opD,
		output logic [2:0] funct3D, 
		output logic funct7b5D,
		input logic StallD, FlushD,
		input  logic [1:0] ImmSrcD,
		// Execute stage signals
		input logic FlushE,
		input logic [1:0] ForwardAE, ForwardBE,
		input logic PCSrcE,
		input logic [2:0] ALUControlE,
		input logic ALUSrcE,
		output logic ZeroE,
		// Memory stage signals
		input logic MemWriteM, 
		output logic [31:0] WriteDataM, ALUResultM,
		input logic [31:0] ReadDataM,
		// Writeback stage signals
		input logic RegWriteW, 
		input logic [1:0] ResultSrcW,
		// Hazard Unit signals 
		output logic [4:0] Rs1D, Rs2D, Rs1E, Rs2E,
		output logic [4:0] RdE, RdM, RdW
);

	// Fetch stage signals
	logic [31:0] PCNextF, PCPlus4F;
	// Decode stage signals
	logic [31:0] InstrD;
	logic [31:0] PCD, PCPlus4D;
	logic [31:0] RD1D, RD2D;
	logic [31:0] ImmExtD;
	logic [4:0]  RdD;
	// Execute stage signals
	logic [31:0] RD1E, RD2E;
	logic [31:0] PCE, ImmExtE;
	logic [31:0] SrcAE, SrcBE;
	logic [31:0] ALUResultE;
	logic [31:0] WriteDataE;
	logic [31:0] PCPlus4E;
	logic [31:0] PCTargetE;
	// Memory stage signals
	logic [31:0] PCPlus4M;
	// Writeback stage signals
	logic [31:0] ALUResultW;
	logic [31:0] ReadDataW;
	logic [31:0] PCPlus4W;
	logic [31:0] ResultW;

	// Fetch stage pipeline register and logic
	mux2    #(32) pcmux(PCPlus4F, PCTargetE, PCSrcE, PCNextF);
	flopenr #(32) pcreg(clk, reset, ~StallF, PCNextF, PCF);
	Adder         pcadd(PCF, 32'h4, PCPlus4F);

	// Decode stage pipeline register and logic
	flopenrc #(96) regD(clk, reset, FlushD, ~StallD, 
											{InstrF, PCF, PCPlus4F},
											{InstrD, PCD, PCPlus4D});
	assign opD       = InstrD[6:0];
	assign funct3D   = InstrD[14:12];
	assign funct7b5D = InstrD[30];
	assign Rs1D      = InstrD[19:15];
	assign Rs2D      = InstrD[24:20];
	assign RdD       = InstrD[11:7];
	
	regfile        rf(clk, RegWriteW, Rs1D, Rs2D, RdW, ResultW, RD1D, RD2D);

	Extender extender (
		InstrD[31:7],
		ImmSrcD,
		ImmExtD
	);
 
	// Execute stage pipeline register and logic
	floprc #(175) regE(clk, reset, FlushE, 
										 {RD1D, RD2D, PCD, Rs1D, Rs2D, RdD, ImmExtD, PCPlus4D}, 
										 {RD1E, RD2E, PCE, Rs1E, Rs2E, RdE, ImmExtE, PCPlus4E});
	
	mux3   #(32)  faemux(RD1E, ResultW, ALUResultM, ForwardAE, SrcAE);
	mux3   #(32)  fbemux(RD2E, ResultW, ALUResultM, ForwardBE, WriteDataE);
	mux2   #(32)  srcbmux(WriteDataE, ImmExtE, ALUSrcE, SrcBE);
	alu           alu(SrcAE, SrcBE, ALUControlE, ALUResultE, ZeroE);
	Adder         branchadd(ImmExtE, PCE, PCTargetE);

	// Memory stage pipeline register
	flopr  #(101) regM(clk, reset, 
										 {ALUResultE, WriteDataE, RdE, PCPlus4E},
										 {ALUResultM, WriteDataM, RdM, PCPlus4M});
	
	// Writeback stage pipeline register and logic
	flopr  #(101) regW(clk, reset, 
										 {ALUResultM, ReadDataM, RdM, PCPlus4M},
										 {ALUResultW, ReadDataW, RdW, PCPlus4W});
	mux3   #(32)  resultmux(ALUResultW, ReadDataW, PCPlus4W, ResultSrcW, ResultW);	
endmodule


module regfile (
		input logic clk, 
		input logic we3, 
		input logic [ 4:0] a1, a2, a3, 
		input logic [31:0] wd3, 
		output logic [31:0] rd1, rd2
);

	logic [31:0] rf[31:0];

	// three ported register file
	// read two ports combinationally (A1/RD1, A2/RD2)
	// write third port on rising edge of clock (A3/WD3/WE3)
	// write occurs on falling edge of clock
	// register 0 hardwired to 0

	always_ff @(negedge clk)
		if (we3) rf[a3] <= wd3;	

	assign rd1 = (a1 != 0) ? rf[a1] : 0;
	assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module Adder (
	input [31:0] a, b,
	output [31:0] y
);
	assign y = a + b;
endmodule

/*
* module extend(input  logic [31:7] instr,
*               input  logic [1:0]  immsrc,
*               output logic [31:0] immext);
*
*   always_comb
*     case(immsrc) 
*                // I-type 
*       2'b00:   immext = {{20{instr[31]}}, instr[31:20]};  
*                // S-type (stores)
*       2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; 
*                // B-type (branches)
*       2'b10:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0}; 
*                // J-type (jal)
*       2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0}; 
*       default: immext = 32'bx; // undefined
*     endcase             
* endmodule
*/

module Extender (
	input logic [31:7] instr,
	input logic [1:0] immsrc,
	output logic [31:0] immext
);
 
	// always_comb
	//   case(immsrc) 
	//     // I-type 
	//     2'b00:   immext = {{20{instr[31]}}, instr[31:20]};  
	//     // S-type (stores)
	//     2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; 
	//     // B-type (branches)
	//     2'b10:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0}; 
	//     // J-type (jal)
	//     2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0}; 
	//     default: immext = 'x; // undefined
	//   endcase

	assign immext =
	(immsrc == 2'b00) ? {{22{instr[31]}}, instr[30:20]} : // I-type
	(immsrc == 2'b01) ? {{21{instr[31]}}, instr[30:25], instr[11:7]} : // S-type
	(immsrc == 2'b10) ? {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0} : // B-type
	(immsrc == 2'b11) ? {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0} :	// J-type
	'x;	// undefined
endmodule


module flopr #(parameter WIDTH = 8)
							(input  logic             clk, reset,
							 input  logic [WIDTH-1:0] d, 
							 output logic [WIDTH-1:0] q);

	always_ff @(posedge clk, posedge reset)
		if (reset) q <= 0;
		else       q <= d;
endmodule

module flopenr #(parameter WIDTH = 8)
								(input  logic             clk, reset, en,
								 input  logic [WIDTH-1:0] d, 
								 output logic [WIDTH-1:0] q);

	always_ff @(posedge clk, posedge reset)
		if (reset)   q <= 0;
		else if (en) q <= d;
endmodule

module flopenrc #(parameter WIDTH = 8)
								(input  logic             clk, reset, clear, en,
								 input  logic [WIDTH-1:0] d, 
								 output logic [WIDTH-1:0] q);

	always_ff @(posedge clk, posedge reset)
		if (reset)   q <= 0;
		else if (en) 
			if (clear) q <= 0;
			else       q <= d;
endmodule

module floprc #(parameter WIDTH = 8)
							(input  logic clk,
							 input  logic reset,
							 input  logic clear,
							 input  logic [WIDTH-1:0] d, 
							 output logic [WIDTH-1:0] q);

	always_ff @(posedge clk, posedge reset)
		if (reset) q <= 0;
		else       
			if (clear) q <= 0;
			else       q <= d;
endmodule

module mux2 #(parameter WIDTH = 8)
						 (input  logic [WIDTH-1:0] d0, d1, 
							input  logic             s, 
							output logic [WIDTH-1:0] y);

	assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
						 (input  logic [WIDTH-1:0] d0, d1, d2,
							input  logic [1:0]       s, 
							output logic [WIDTH-1:0] y);

	assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

module InstructionMemory (
		input  logic [31:0] address,		// program counter
		output logic [31:0] instruction_read		// fetched instruction
);
	logic [31:0] RAM[0:63];		// 64 x 32-bit instruction memory

	initial $readmemh("instructions.hex", RAM);		// load instructions from file

	assign instruction_read = RAM[address[31:2]];		// word-aligned access (bit slicing)

	final begin
		// dumps memory contents to a file at the end of simulation
		$writememh("./dump/instructionMemory.hex", RAM);
	end
endmodule

module DataMemory (
		input logic clk,
		write_enabled,
		input logic [31:0] address,
		data_to_write,		// data to write
		output logic [31:0] data_read		// data read
);

	logic [31:0] RAM[0:63];		// 64 x 32-bit words

	assign data_read = RAM[address[31:2]];		// word-aligned read

	always_ff @(posedge clk)
		if (write_enabled)
			RAM[address[31:2]] <= data_to_write;		// word-aligned write

	final begin
		// dumps memory contents to a file at the end of simulation
		$writememh("./dump/dataMemory.hex", RAM);
	end
endmodule

module alu(input  logic [31:0] a, b,
					 input  logic [2:0]  alucontrol,
					 output logic [31:0] result,
					 output logic        zero);

	logic [31:0] condinvb, sum;
	logic        v;              // overflow
	logic        isAddSub;       // true when is add or subtract operation

	assign condinvb = alucontrol[0] ? ~b : b;
	assign sum = a + condinvb + alucontrol[0];
	assign isAddSub = ~alucontrol[2] & ~alucontrol[1] |
										~alucontrol[1] &  alucontrol[0];

	// always_comb
	//   case (alucontrol)
	//     3'b000:  result = sum;         // add
	//     3'b001:  result = sum;         // subtract
	//     3'b010:  result = a & b;       // and
	//     3'b011:  result = a | b;       // or
	//     3'b100:  result = a ^ b;       // xor
	//     3'b101:  result = sum[31] ^ v; // slt
	//     3'b110:  result = a << b[4:0]; // sll
	//     3'b111:  result = a >> b[4:0]; // srl
	//     default: result = 32'bx;
	//   endcase

	assign result =
		(alucontrol == 3'b000) ? sum :            // add
		(alucontrol == 3'b001) ? sum :            // sub
		(alucontrol == 3'b010) ? a & b :          // and
		(alucontrol == 3'b011) ? a | b :          // or
		(alucontrol == 3'b100) ? a ^ b :          // xor
		(alucontrol == 3'b101) ? sum[31] ^ v :    // slt
		(alucontrol == 3'b110) ? a << b[4:0] :    // sll
		(alucontrol == 3'b111) ? a >> b[4:0] :    // srl
		'x;

	assign zero = (result == 32'b0);
	assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub;
endmodule
