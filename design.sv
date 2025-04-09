`timescale 1ns / 1ns

module TestBench ();
	logic clk, reset, write_to_memory;
	logic [31:0] write_data, data_address;

	// instantiates device under test (top level module)
	Top dut (
		clk,
		reset,
		write_to_memory,
		write_data,
		data_address
	);

	// initializes test
	initial begin
		reset <= 1;
		#22;		// 2.2 cycles
		reset <= 0;
	end

	// generates clock
	initial begin
	        clk <= 0;
	        forever #5 clk = ~clk;		// 5ns high + 5ns low = 10ns → 100MHz
	end

	initial begin
		$dumpfile("waveform.vcd");		// indicates file.vcd (Value Change Dump)
		$dumpvars(0, dut);				// dump signals from the module

		#500;
		// $dumpon;
		// $dumpoff;
		$finish;
	end

	// checks results
	always @(negedge clk) begin
		if (write_to_memory) begin
			if (data_address === 100 & write_data === 25) begin
					$display("Simulation succeeded!");
					$stop;
			end
			else if (data_address !== 96) begin
					$display("Simulation failed!");
					$stop;
			end
		end
	end
endmodule

// top level module
module Top (  
		input logic clk, reset,
		output logic write_to_memory,
		output logic [31:0] write_data,
		data_address
);

	logic [31:0] PC, instruction, data_read;

	// instantiate processor and memories
	Processor riscvsingle (
		clk,
		reset,
		instruction,
		data_read,
		write_to_memory,
		PC,
		data_address,
		write_data
	);

	InstructionMemory instMemory (
		PC,
		instruction
	);

	DataMemory dataMemory (
		clk,
		write_to_memory,
		data_address,
		write_data,
		data_read
	);
endmodule

module Processor (
		input logic clk, reset,
		input logic [31:0] instruction,
		data_read,
		output logic write_to_memory,
		output logic [31:0] PC,
		ALU_result,		// data_address
		write_data
);
	logic ALU_source, write_to_register, jump, zero, PC_source;
	logic [1:0] result_source, immediate_source;
	logic [2:0] ALU_control;

	Controller controller (
		instruction[30],
		zero,
		instruction[14:12],
		instruction[6:0],
		write_to_memory,
		PC_source,
		ALU_source,
		write_to_register,
		jump,
		result_source,
		immediate_source,
		ALU_control
	);

	Datapath datapath (
		clk,
		reset,
		PC_source,
		ALU_source,
		write_to_register,
		result_source,
		immediate_source,
		ALU_control,
		instruction,
		data_read,
		zero,
		PC,
		write_data,
		ALU_result
	);
endmodule

module InstructionMemory (
		input  logic [31:0] address,		// program counter
		output logic [31:0] instruction_read		// fetched instruction
);
	logic [31:0] RAM[0:63];		// 64 x 32-bit instruction memory

	initial $readmemh("instructions.hex", RAM);		// load instructions from file

	assign instruction_read = RAM[address[31:2]];		// word-aligned access (bit slicing)

	final begin
		$writememh("./dump/instructionMemory.hex", RAM);		// dump memory contents to a file at the end of simulation
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
		$writememh("./dump/dataMemory.hex", RAM);		// dump memory contents to a file at the end of simulation
	end
endmodule

module Controller (
		input logic funct7_b5,
		zero,
		input logic [2:0] funct3,
		input logic [6:0] opcode,
		output logic write_to_memory,
		PC_source,
		ALU_source,
		write_to_register,
		jump,
		output logic [1:0] result_source,
		output logic [1:0] immediate_source,
		output logic [2:0] ALU_control
);

	logic branch;
	logic [1:0] ALU_operation;

	MainDecoder maindecoder (
		opcode,
		write_to_memory,
		branch,
		ALU_source,
		write_to_register,
		jump,
		result_source,
		immediate_source,
		ALU_operation
	);

	ALUDecoder ALUdecoder (
		opcode[5],
		funct7_b5,
		ALU_operation,
		funct3,
		ALU_control
	);

	assign PC_source = branch & zero;
endmodule

module MainDecoder (
		input logic [6:0] opcode,
		output logic write_to_memory,
		branch,
		ALU_source,
		write_to_register,
		jump,
		output logic [1:0] result_source,
		immediate_source,
		ALU_operation
);
	logic [10:0] controls;

	always_comb begin
		case (opcode)
			7'b0000011:
				controls = 11'b1_00_1_0_01_0_00_0;	// lw
			7'b0100011:
				controls = 11'b0_01_1_1_00_0_00_0;	// sw
			7'b0110011:
				controls = 11'b1_xx_0_0_00_0_10_0;	// R-type
			7'b1100011:
				controls = 11'b0_10_0_0_00_1_01_0;	// beq
			default:
				controls = 11'bx_xx_x_x_xx_x_xx_x;	// non-implemented instruction
		endcase
	end

	// splits the control vector into individual signals
	assign {write_to_register, immediate_source, ALU_source, write_to_memory, result_source, branch, ALU_operation, jump} = controls;
endmodule

module ALUDecoder (
		input logic opcode_b5,
		funct7_b5,
		input logic [1:0] ALU_operation,
		input logic [2:0] funct3,
		output logic [2:0] ALU_control
);
	logic is_rtype_sub;
	assign is_rtype_sub = funct7_b5 & opcode_b5;		// TRUE for R-type subtract instruction

	always_comb
		case (ALU_operation)
			2'b00:
				ALU_control = 3'b000;		// addition
			2'b01:
				ALU_control = 3'b001;		// subtraction
			default:
				case (funct3)		// R-type or I-type ALU
					3'b000:
						if (is_rtype_sub)
							ALU_control = 3'b001;		// sub
						else
							ALU_control = 3'b000;		// add, addi
					3'b010:
						ALU_control = 3'b101;		// slt, slti
					3'b110:
						ALU_control = 3'b011;		// or, ori
					3'b111:
						ALU_control = 3'b010;		// and, andi
					default:
						ALU_control = 3'bxxx;		// ???
				endcase
		endcase
endmodule

module Datapath (
	input logic clk, reset,
	PC_source,
	ALU_source,
	write_to_register,
	input logic [1:0] result_source,
	immediate_source,
	input logic [2:0] ALU_control,
	input logic [31:0] instruction,
	data_read,
	output logic zero,
	output logic [31:0] PC,
	write_data,
	ALU_result
);
	logic [31:0] PC_next, PC_plus4, PC_target;
	logic [31:0] immediate_extended;		// ¿ de onde vem ?
	logic [31:0] source_A, source_B;
	logic [31:0] result;

	// next program counter logic
	FlipFlopR #(32) PCRegister (
		clk, reset,
		PC_next,
		PC
	);

	Adder PCplus4Adder  (
		PC,
		32'd4,
		PC_plus4
	);

	Adder PCbranchAdder (
		PC,
		immediate_extended,
		PC_target
	);
	
	// MuxNto1 #(32, 2) PCmux (
	// 	.in({PC_target, PC_plus4}),
	// 	.sel(TEST_source),
	// 	.out(PC_next)
	// );

	Mux2to1 #(32) PCMux (
		PC_plus4, PC_target,
		PC_source,
		PC_next
	);

	// register file logic
	RegisterFile registerFile (
		clk,
		write_to_register,
		instruction[19:15], instruction[24:20],	instruction[11:7],		// rs1|rs2|rd
		result,
		source_A, write_data
	);

	Extender extender (
		immediate_source,
		instruction[31:7],
		immediate_extended
	);

	// ALU logic
	Mux2to1 #(32) sourceBMux (
		write_data, immediate_extended,
		ALU_source,
		source_B
	);

	ALU alu (
		ALU_control,
		source_A, source_B,
		zero,
		ALU_result
	);

	MuxNto1 #(32, 3) resultMux (
		.in({32'b0, data_read, ALU_result}),
		.sel(result_source),
		.out(result)
	);
endmodule

module FlipFlopR #(
		parameter WIDTH = 8
) (
		input logic clk, reset,
		input logic [WIDTH-1:0] d,
		output logic [WIDTH-1:0] q
);
	always_ff @(posedge clk, posedge reset) begin
		if (reset)
			q <= 0;
		else
			q <= d;
	end
endmodule

module Adder (
		input  logic [31:0] a, b,
		output logic [31:0] sum
);
	assign sum = a + b;
endmodule

module Mux2to1 #(
		parameter WIDTH = 8
) (
		input  logic [WIDTH-1:0] in0, in1,
		input  logic             sel,
		output logic [WIDTH-1:0] out
);
	assign out = sel ? in1 : in0;
endmodule

module MuxNto1 #(
	parameter WIDTH = 32,
	parameter N     = 4
)(
    input  logic [N-1:0][WIDTH-1:0] in,		// inputs
    input  logic [$clog2(N)-1:0] sel,		// selector
    output logic [WIDTH-1:0] out
);
    always_comb begin
	out = (sel < N) ? in[sel] : 'x;
    end
endmodule

module RegisterFile (
		input logic clk,
		input logic write_enabled,
		input logic [4:0] register_rource1, register_rource2, destination_register, // rs1/rs2/rd
		input logic [31:0] data_to_write,
		output logic [31:0] data_read1, data_read2
);
	logic [31:0] register_file[31:0];  // 32 registers, each 32 bits wide

	// Three-ported register file:
	// - Two ports for combinational reads (A1/RD1, A2/RD2)
	// - One port for clocked writes (A3/WD3/WE3)
	// - Register 0 is hardwired to 0

	always_ff @(posedge clk) begin
		if (write_enabled) register_file[destination_register] <= data_to_write;
	end

	assign data_read1 = (register_rource1 != 0) ? register_file[register_rource1] : '0;	// returns 0 if accessing register 0
	assign data_read2 = (register_rource2 != 0) ? register_file[register_rource2] : '0;	// returns 0 if accessing register 0
endmodule

module Extender (
		input logic [1:0] immediate_source,
		input logic [31:7] instruction,
		output logic [31:0] immediate_extended
);

	logic [31:0] instr_full;

	// Preenche os bits 6 a 0 com 0 para facilitar acesso com índices fixos
   	assign instr_full = {instruction, 7'b0};

	assign immediate_extended =
		(immediate_source == 2'b01) ? {{20{instr_full[31]}}, instr_full[31:25], instr_full[11:7]} :
		(immediate_source == 2'b11) ? {{12{instr_full[31]}}, instr_full[19:12], instr_full[20], instr_full[30:21], 1'b0} :
		'x;
endmodule

module ALU (
		input logic [2:0] ALU_control,
		input logic [31:0] A, B,
		output logic zero,
		output logic [31:0] result
);

	logic of,		// Overflow flag
	isAddorSub;		// True for add or subtract operations
	logic [4:0] shift_amount;
	logic [31:0] sum;

	// prepare conditional inversion of 'B' and calculate sum
	assign sum = A + (ALU_control[0] ? ~B : B) + ALU_control[0];

	// determine if the operation is addition or subtraction
	assign isAddorSub = ~ALU_control[2] & ~ALU_control[1] | ~ALU_control[1] & ALU_control[0];

	// zero flag: true if result is zero
	assign zero = (result == 32'b0);

	// overflow detection
	assign of = ~(ALU_control[0] ^ A[31] ^ B[31]) & (A[31] ^ sum[31]) & isAddorSub;

	assign shift_amount = B[4:0];

	// // operations
	// always_comb begin
	// 	case (ALU_control)
	// 		3'b000:
	// 			result = sum;		// Add
	// 		3'b001:
	// 			result = sum;		// Subtract
	// 		3'b010:
	// 			result = A & B;		// AND
	// 		3'b011:	
	// 			result = A | B;		// OR
	// 		3'b100:
	// 			result = A ^ B;		// XOR
	// 		3'b101:
	// 			result = sum[31] ^ of;		// SLT (set less than)
	// 		3'b110:
	// 			result = A << shift_amount;		// SLL (shift left logical)
	// 		3'b111:
	// 			result = A >> shift_amount;		// SRL (shift right logical)
	// 		default:
	// 			result = 'x;		// Undefined operation
	// 	endcase
	// end

	// ¿ operations ?
	assign result =
		(ALU_control == 3'b000) ? sum :
		(ALU_control == 3'b001) ? sum :
		(ALU_control == 3'b010) ? A & B :
		(ALU_control == 3'b011) ? A | B :
		(ALU_control == 3'b100) ? A ^ B :
		(ALU_control == 3'b101) ? sum[31] ^ of :
		(ALU_control == 3'b110) ? A << B[4:0] :
		(ALU_control == 3'b111) ? A >> B[4:0] :
		'x;
endmodule