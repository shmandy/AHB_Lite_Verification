//////////////////////////////////////////////////////////////
// ahb_lite_tb.sv - AHB-Lite Slave Testbench
//
// Authors: 
//	Andrew Elliott (andy@pdx.edu)
// 
// Date: 3/14/2018
// Version 0.1
//
//
// Revisions:
//
//
//
// Description:
// ------------
// This is an AHB-LIte Testbench for validating a 32-bit slave memory device
// The testbench is used to validate an AHB-Slave using the AMBA3 AHB-Lite Specification
//
// Usage Notes:
// This file does not have any test sources. The TOP module is used to feed input
// into the tasks using the provided transaction data class (t_data) and the program driver.
//
// Note: This needs to be configured for TBX Mode (add pragmas)
//
////////////////////////////////////////////////////////////////

import ahb_lite_defs::*;	// Import definitions package

// DUT Driver module - connects to interface
// Connects to (2) AHB-Lite Interfaces
// MASTER modport - AHB Lite Master Channel
// DUMMY_SLAVE modport - AHB Lite Slave Channel 3 (default)
interface ahb_lite_tb_interface(
	ahb_lite_bus.MASTER master, 
	ahb_lite_bus.DUMMY_SLAVE slave
	);
	// pragma attribute ahb_lite_tb_interface partition_interface_xif	
	
	// Drive Unused Signals to Ground (0)
	assign master.HPROT = '0;
	assign master.HMASTLOCK = '0;
	
	
	
	/********************************************************************/
	// 				TASKS: Single Transactions							//
	//																	//
	//		Every transaction is a single in-out process				//
	// 		All sequences are driven by the sequencer					//
	// 		This does create additional overhead in the Emulation		//
	//		As the TB is required to provide all data sets				//
	/********************************************************************/
	
	// Task waits for a clock cycle
	// Replaces #CLOCK_PERIOD statement for portability
	task  wait_cycle(); // pragma tbx xtf
		begin
			@(posedge master.HCLK);	// Wait one cycle
		end
	endtask: wait_cycle
	
	// Single Transaction
	// Actions defined by packet
	task single_trx( 
		input testdata_bfm_t packet_in,
		output testdata_bfm_t packet_out
		); // pragma tbx xtf
	
		// Load Data In:
		master.HADDR 	<= packet_in.HADDR;			// Set Address
		master.HWDATA 	<= packet_in.HWDATA;		// Set Data
		master.HWRITE 	<= packet_in.HWRITE;		// Set Write Mode
		master.HSIZE 	<= packet_in.HSIZE;			// Set Transfer Size
		master.HBURST 	<= packet_in.HBURST;		// Set Burst Type
		master.HTRANS 	<= packet_in.HTRANS;		// Set Transfer Type
	
		@(posedge master.HCLK);						// Wait one clock cycle
		
		// Read data out
		packet_out 			= packet_in;			// Clone original packet
		packet_out.HRDATA 	= master.HRDATA;		// Get Data Output
		packet_out.HREADY 	= master.HREADY;		// Get Ready State
		packet_out.HRESP 	= master.HRESP;			// Get Response
		
	endtask: single_trx

endinterface: ahb_lite_tb_interface 
