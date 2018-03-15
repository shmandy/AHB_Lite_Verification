//////////////////////////////////////////////////////////////
// ahb_lite_defs.sv - AHB-Lite Interface and Module definitions
//
// Author: Andrew Elliott (andy@pdx.edu)
// Date: 3/5/2018
//
// Version 0.2
//
//
// Revisions:
// 3/8: Corrected SEL signals and ADDRESSES
// 3/9: Added enum typedefs for all control signals
// 
//
//
// Description:
// ------------
// This AHB-Lite definitions package is used for two-slave interface and
// dual-port RAM module.
////////////////////////////////////////////////////////////////

// Definitions for Memory Controller
package ahb_lite_defs;
	
	
	/////////////////////////////
	// Testbench Configuration //
	/////////////////////////////
	
	parameter CLOCK_PERIOD	=	10;		// Test bench Clock Period - SIMULATION MODE
	parameter CLOCK_DC	=	5;		// Internally-generated clock duty-cycle (1/2 period) - EMULATION MODE
	

	//////////////////////////////////
	// AHB-Lite Slave Configuration //
	//////////////////////////////////
	
 	// Dual-port RAM Configuration (Memory Definitions):
	parameter BYTES_PER_WORD 	= 4;			// Bytes per word
	parameter BYTE_SIZE		= 8;			// Bits per Byte
	parameter DATAWIDTH		= 32;		// Data word width in bits (32-bit)
	parameter MEMDEPTH 		= 1024;		// Memory Depth (in words)
	parameter ADDRWIDTH 	= 12;		// Data Address Width (in bits)
	
	// Slave Configuration
	parameter MAX_WAITS		= 16;		// Maximum number of wait states before backoff

	
	////////////////////////////////
	// AHB-Lite Bus Configuration //
	////////////////////////////////
	
	// AHB-Lite Bus Configuration
	parameter AHB_DATAWIDTH	 = 32;		// 32-bit Data Bus
	parameter AHB_ADDRWIDTH	 = 32;		// 32-bit MIMO Address Bus
	parameter AHB_MEM_RANGE	 = 24;		// 24-bit internal memory range (32 - 8)
	
    // AHB-Lite Slave Addresses [31:24]
	parameter SLAVE0_ADDR 		=	8'h01;			// Slave 0 Address
	parameter SLAVE1_ADDR 		=	8'h02;			// Slave 1 Address
	parameter DUMMYSLAVE_ADDR 	=	8'h04;			// Slave 3 Address (Dummy)
	
	// AHB-Lite Slave Select IDs:
	parameter SLAVE0_SEL 	= 3'b001;		// Select Slave 0
	parameter SLAVE1_SEL	= 3'b010;		// Select Slave 1
	parameter DUMMY_SEL 	= 3'b100;		// Select Dummy Device (Testbench Modport)
	 
	// AHB-Lite Transfer Types
	typedef enum logic [1:0]{
		IDLE 	= 2'b00,					// No data transfer required
		BUSY 	= 2'b01,					// Enable master to insert idle cycle
		NONSEQ 	= 2'b10,					// Indicate single transfer, or first transfer of burst
		SEQ 	= 2'b11						// Remaining transfer in burst are sequential
	} htrans_t;
	
	// AHB-Lite Burst Transfer Types (*master)
	typedef enum logic [2:0]{
		SINGLE 	= 3'b000,				// Single Burst
		INCR	= 3'b001,				// Incrementing burst of undefined length	
		WRAP4	= 3'b010,				// 4-beat wrapping burst
		INCR4	= 3'b011,				// 4-beat incrementing burst
		WRAP8	= 3'b100,				// 8-beat wrapping burst
		INCR8	= 3'b101,				// 8-beat incrementing burst
		WRAP16	= 3'b110,				// 16-beat wrapping burst
		INCR16	= 3'b111					// 16-beat incrementing burst
	} hburst_t;
	
	// AHB-Lite Trnsfer Size Selection (*master):
	typedef enum logic [2:0]{
		BYTE			= 3'b000,			// Single Byte (8-bits)
		HALFWORD		= 3'b001,			// Two Bytes "Halfword"
		WORD			= 3'b010,			// Four Bytes "Word"
		DOUBLE_WORD	= 3'b011,				// Double Word	(NOT SUPPORTED)
		LINE_4_WORD	= 3'b100,				// Quad Word 		(NOT SUPPORTED)
		LINE_8_WORD	= 3'b101,				// Eight Words	(NOT SUPPORTED)
		LINE_16_WORD	= 3'b110,			// Sixteen Words 	(NOT SUPPORTED)
		LINE_32_WORD 	= 3'b111 			// 32 Words 		(NOT SUPPORTED)
	} hsize_t;
	
	// AHB-Lite Write Signal (*master):
	typedef enum logic  {
		READ	= 1'b0,						// Perform a read operation (from slave)
		WRITE	= 1'b1						// PErform a write operation (to slave)
	}hwrite_t;
	
	// AHB-Lite Ready Signal (slave & master):
	typedef enum logic {
		WAIT 	= 1'b0,				// Extend the transfer (wait)
		READY 	= 1'b1				// Completed (ready) signal
	}hready_t;
	
	// AHB-Lite Response Signal (*slave):
	typedef enum logic {
		OKAY 	= 1'b0,					// Transfer Status is OKAY
		ERROR	= 1'b1					// Transfer ERROR
	}hresp_t;

	
	
	// Test Data Class Object
	// Test data "packet"
	class testdata_t;

		// Class Data Members: //
		
		// Address and Data (RANDOM):
		rand logic [AHB_DATAWIDTH:0] 	data_out;			// Randomized Data Out (HWDATA)
		rand logic [AHB_MEM_RANGE-1:0]	random_mem;			// Randomized Memory Select
		rand logic [1:0] slave_select;
		constraint legal {
			slave_select >= 1;								// Constrained to SLAVE 0 and 1
			slave_select <= 2;
		};
		
		// Data Members (SET)
		logic [AHB_ADDRWIDTH-1:0] address;					// Address (HADDR)
		logic [AHB_DATAWIDTH:0] data_in;					// Incoming Data (HRDATA)
		
		// Control Signals (master only) Outputs:
		hwrite_t	HWRITE;	// Write Enable
		hsize_t 	HSIZE;	// Transfer Size
		hburst_t 	HBURST;	// Burst Type
		htrans_t 	HTRANS;	// Transfer Type
		
		// Control Signal Inputs: (write to these)
		hready_t HREADY;
		hresp_t HRESP;
		
		// Initialize New Object
		function new();
			address = '0;									// Clear Address
			HSIZE = WORD;									// Set Size to WORD
			HBURST = SINGLE;								// Set BURST to SINGLE
			HTRANS = NONSEQ;								// Set Transfer type to NONSEQ
			HWRITE = READ;									// Set Transfer to READ
		endfunction
		
		
		// Deep copy from other object:
		task copy_from(input testdata_t pkt);
			begin
				address = pkt.address;
				data_out = pkt.data_out;
				data_in = pkt.data_in;
				HSIZE = pkt.HSIZE;
				HBURST = pkt.HBURST;
				HTRANS = pkt.HTRANS;
				HWRITE = pkt.HWRITE;
			end
		endtask
		
		
		// Set Address to Random Location
		// Choose the Slave Address at random (0 or 1)
		// Chose the SIZE at Random
		// Chose the OFFSET at random
		function void setRandom(
			input logic constrain_range
			);
			begin
				// Random Address and Slave
				if(constrain_range)
					address = { 6'b0, slave_select, 12'b0, random_mem[ADDRWIDTH-1:0] }; // Don't trip bounds err
				else
					address = { 6'b0, slave_select, random_mem };	// Could generate outside mem bounds
				
				// Random Size: 
				case(random_mem[13:11])
					2'b00:	HSIZE = BYTE;
					2'b01:	HSIZE = HALFWORD;
					default: HSIZE = WORD;
				endcase
			end
		endfunction
		
		
		// Compare Results, return 1 data out == data in
		function logic compare();
			begin
				case(HSIZE)
					BYTE:	begin
						// Offset
						case(address[1:0])
							2'b00:	compare = ( data_out[7:0] 	== data_in[7:0] );		// Byte 0
							2'b01:	compare = ( data_out[15:8] 	== data_in[15:8] );		// Byte 1
							2'b10:	compare = ( data_out[23:16] == data_in[23:16] );	// Byte 2
							2'b11:	compare = ( data_out[31:24] == data_in[31:24] );	// Byte 3
						endcase
					end
					
					HALFWORD:	begin
						if(address[1:0] == 2'b00) compare = ( data_out[15:0] == data_in[15:0] );		// Lower HWORD
						else if(address[1:0] == 2'b10) compare = ( data_out[31:16] == data_in[31:16] );	// Upper HWORD
						else compare = 0;
					end
					
					WORD:	compare = (data_in == data_out);	// Word
					default:	compare = 0;					// Error
				endcase
			end
		endfunction
		
		
	endclass: testdata_t
	

endpackage: ahb_lite_defs