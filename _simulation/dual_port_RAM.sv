//////////////////////////////////////////////////////////////
// dual_port_RAM.sv - A simple dual-port RAM module
//
// Author: Andrew Elliott (andy@pdx.edu)
// Date: 3/5/2018
//
// Version 0.4
//
//
// Revisions:
// 3/9 mapped q_b output to input on write
// 3/12 Split into byte access
// 3/13 Changed RAM Definitions

// Description:
// ------------
// A simple dual-port RAM module with parametrized settings.
////////////////////////////////////////////////////////////////

import ahb_lite_defs::*; // Import package

module dual_port_RAM(
	output logic [DATAWIDTH-1:0] q_a,			// Data Out A
	output logic [DATAWIDTH-1:0] q_b,			// Data Out B
	input logic clk_a,						// Clock A
	input logic clk_b,						// Clock B
	input logic [ADDRWIDTH-1:0] addr_a,			// Address A
	input logic [ADDRWIDTH-1:0] addr_b,			// Address B
	input logic [DATAWIDTH-1:0] data_a,			// Data Input A
	input logic [DATAWIDTH-1:0] data_b,			// Data Input B
	input logic we_a,							// Write Enable A
	input logic we_b,							// Write Enable B
	input hsize_t	size_a, size_b				// Size Select Inputs	
	
	);
	
	// Memory Mapping
	logic [1:0] offset_a, offset_b;
	logic [11:0] address_a, address_b;
	
	assign offset_a = addr_a[1:0];
	assign offset_b = addr_b[1:0];
	assign address_a = addr_a[11:2];
	assign address_b = addr_b[11:2];
	
	// 32-bit Byte Memory:
	logic [DATAWIDTH-1:0] RAM [MEMDEPTH];		// Shared Memory Module

	
	// Port A Operations:
	always_ff @(posedge clk_a) begin
		// Store to memory
		if(we_a) begin
				if(size_a == BYTE) begin
				unique case(offset_a)
					2'b00:	RAM[address_a] <= { RAM[address_a][31:8], data_a[7:0] };							// Byte 0
					2'b01:	RAM[address_a] <= { RAM[address_a][31:16], data_a[15:8], RAM[address_a][7:0] };		// Byte 1
					2'b10:	RAM[address_a] <= { RAM[address_a][31:24], data_a[23:16], RAM[address_a][15:0] };	// Byte 2
					2'b11:	RAM[address_a] <= { data_a[31:24], RAM[address_a][23:0] };							// Byte 3 
				endcase
			end
		
			// Half Word (Upper or Lower)
			else if(size_a == HALFWORD) begin
				if(offset_a == 2'b00) 		RAM[address_a] <= { RAM[address_a][31:16], data_a[15:0] };			// Lower Halfword
				else if(offset_a == 2'b10) 	RAM[address_a] <= { data_a[31:16], RAM[address_a][15:0] };			// Upper Halfword
				//else RAM[address_a] <= RAM[address_a];
			end
		
			// Word
			else if(size_a == WORD)	RAM[address_a] <= data_a;

			// Error
			//else RAM[address_a] <= RAM[address_a];
		
		end // END WRITE
		
		// Read from memory
		else begin
			
			// Byte Select
			if(size_a == BYTE) begin
				unique case(offset_a)
					2'b00:	q_a <= { 24'b0, RAM[address_a][7:0] };					// Byte 0 (LSB)
					2'b01:	q_a <= { 16'b0, RAM[address_a][15:8], 8'b0 };			// Byte 1
					2'b10:	q_a <= { 8'b0, RAM[address_a][23:16], 16'b0 };			// Byte 2
					2'b11:	q_a <= { RAM[address_a][31:24], 42'b0 };					// Byte 3
				endcase
			end
			
			// Half Word (Upper or Lower)
			else if(size_a == HALFWORD) begin
				if(offset_a == 2'b00)		q_a <= { 16'b0, RAM[address_a][15:0] };		// Read Lower Word
				else if(offset_a == 2'b10)	q_a <= { RAM[address_a][31:16], 16'b0 };		// Read Upper Word
				else q_a <= '0;													// Bad Offset Error
			end
			
			else if(size_a == WORD) q_a <= RAM[address_a];							// Read Word
			else q_a <= '0;														// Error
		end
	end
	
	// Port B Operations:
	always_ff @(posedge clk_b) begin
		if(we_b) begin
					if(size_b == BYTE) begin
					unique case(offset_b)
						2'b00:	RAM[address_b] <= { RAM[address_b][31:8], data_b[7:0] };						// Byte 0
						2'b01:	RAM[address_b] <= { RAM[address_b][31:16], data_b[15:8], RAM[address_b][7:0] };	// Byte 1
						2'b10:	RAM[address_b] <= { RAM[address_b][31:24], data_b[23:16], RAM[address_b][15:0] };// Byte 2
						2'b11:	RAM[address_b] <= { data_b[31:24], RAM[address_b][23:0] };						// Byte 3 
					endcase
				end
			
				// Half Word (Upper or Lower)
				else if(size_b == HALFWORD) begin
					if(offset_b == 2'b00) 			RAM[address_b] <= { RAM[address_b][31:16], data_b[15:0] };		// Lower Halfword
					else if(offset_b == 2'b10) 	RAM[address_b] <= { data_b[31:16], RAM[address_b][15:0] };		// Upper Halfword
					//else RAM[address_b] <= RAM[address_b];
				end
			
				// Word
				else if(size_b == WORD)	RAM[address_b] <= data_b;

				// Error
				//else RAM[address_b] <= RAM[address_b];
			
			end // END WRITE
		
		// Read from memory
		else begin
			// Byte Select
			if(size_b == BYTE) begin
				unique case(offset_b)
					2'b00:	q_b <= { 24'b0, RAM[address_b][7:0] };					// Byte 0 (LSB)
					2'b01:	q_b <= { 16'b0, RAM[address_b][15:8], 8'b0 };			// Byte 1
					2'b10:	q_b <= { 8'b0, RAM[address_b][23:16], 16'b0 };			// Byte 2
					2'b11:	q_b <= { RAM[address_b][31:24], 42'b0 };					// Byte 3
				endcase
			end
			
			// Half Word (Upper or Lower)
			else if(size_b == HALFWORD) begin
				if(offset_b == 2'b00)		q_b <= { 16'b0, RAM[address_b][15:0] };		// Read Lower Word
				else if(offset_b == 2'b10)	q_b <= { RAM[address_b][31:16], 16'b0 };		// Read Upper Word
				else q_b <= '0;													// Bad Offset Error
			end
			
			// Read Word
			else if(size_b == WORD) q_b <= RAM[address_b];							
			else q_b <= '0;														// Error
		end
	end
endmodule: dual_port_RAM