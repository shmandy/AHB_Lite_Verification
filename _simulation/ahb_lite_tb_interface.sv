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
	ahb_lite_bus.DUMMY_SLAVE slave);
	
	
	// Drive Unused Signals to Ground (0)
	assign master.HPROT = '0;
	assign master.HMASTLOCK = '0;
	
	
	/********************************************************************/
	// 			TASKS: Map MASTER bus to packet data				//
	/********************************************************************/
	
	// Map a testdata_t to the master bus:
	// No Internal Clock Signals
	task master_write(
		input testdata_t test_packet
		);
		begin
			master.HADDR = test_packet.address;		// Set Address
			master.HWDATA = test_packet.data_out;	// Set Data
			master.HWRITE = test_packet.HWRITE;		// Set Write Mode
			master.HSIZE = test_packet.HSIZE;		// Set Transfer Size
			master.HBURST = test_packet.HBURST;		// Set Burst Type
			master.HTRANS = test_packet.HTRANS;		// Set Transfer Type
		end
	endtask: master_write
	
	
	// Map MASTER output to a data class object
	// No Internal Clock Signals
	task automatic master_read(
		ref testdata_t test_packet
		);
		begin
			test_packet.data_out = master.HRDATA;	// Get Data Output
			test_packet.HREADY = master.HREADY;		// Get Ready State
			test_packet.HRESP = master.HRESP;		// Get Response
		end
	endtask: master_read

	
	/********************************************************************/
	// 				TASKS: Single Transactions						//
	/********************************************************************/
	
	// Task waits for a clock cycle
	// Repalces #CLOCK_PERIOD statement for portablility
	task automatic wait_cycle();
		begin
			@(posedge master.HCLK);	// Wait one cycle
		end
	endtask: wait_cycle
	
	// Single Transaction
	// Actions defined by packet
	task automatic single_trx( ref testdata_t test_packet );
	
		@(posedge master.HCLK);		// Advance Clock
		master_write(test_packet);		// Write data to BUS

		while (!master.HREADY);	    	// insert wait state till HREADY is active
		
		@(posedge master.HCLK);        	// salve samples the information on this Clock cycle.
		master_read(test_packet);		// Read response and get data from Slave (RAM)

	endtask: single_trx
	
	
	// Perform Read:
	task automatic single_read( ref testdata_t test_packet );
		
		// Configure test_data input for read operation:
		test_packet.HWRITE = READ;		// Set WRITE flag to READ
		test_packet.HBURST = SINGLE;	// Set to Single
		
		// Perform Transaction
		single_trx(test_packet);
	
	endtask: single_read
	
	
	// Perform Write:
	task automatic single_write( ref testdata_t test_packet );	
		
		// Configure test_data input for read operation:
		test_packet.HWRITE = WRITE;		// Set write enable to WRITE
		test_packet.HBURST = SINGLE;	// Set to Single
		
		// Perform Transaction
		single_trx(test_packet);
		
	endtask: single_write
	
	/********************************************************************/
	// 				TASKS: Sequence Transactions					//
	/********************************************************************/
	
	// Update with Sequence Transaction Tasks
	

endinterface: ahb_lite_tb_interface