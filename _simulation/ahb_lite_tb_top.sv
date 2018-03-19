//////////////////////////////////////////////////////////////
// ahb_lite_tb_top.sv - AHB-Lite Slave Testbench TOP module (driver)
//
// Author:
// Andrew Elliott (andy@pdx.edu)
// 
// Date: 3/13/2018
// Version 0.2
//
//
// Revisions:
//
//
//
// Description:
// ------------
// This is the top module for an AHB-LIte Testbench
// The testbench is used to validate an AHB-Slave using the AMBA3 AHB-Lite Specification
//
// Usage Notes:
//
// The TOP module contains and links the following modules:
//		ahb_lite_bus				-	An interface for AHB-Lite Devices
//		ahb_lite_slave_wrapper		-	The DUT - Containing a Dual-port RAM and two slave interfaces
//		ahb_lite_tb_driver		-	The driver (program) containting all test data
//		ahb_lite
//
//
////////////////////////////////////////////////////////////////

import ahb_lite_defs::*; // Import package

// `define SCOPE_INTERNAL	// Enable Exposed RAM Signals 

module ahb_lite_tb_top();
	
	// Expose Internal signals
	`ifdef SCOPE_INTERNAL
		// RAM:
		logic we_a, we_b;
		logic [ADDRWIDTH-1:0] addr_a, addr_b;
		logic [DATAWIDTH-1:0] data_a, data_b, q_a, q_b;
		
		assign we_a = wrapper.we_a;
		assign we_b = wrapper.we_b;
		assign addr_a = wrapper.addr_a;
		assign addr_b = wrapper.addr_b;
		assign data_a = wrapper.data_a;
		assign data_b = wrapper.data_b;
		
		// Memory Controller MC0
		logic MC0_error_bounds, MC0_error_size, MC0_error_no_idle, MC0_error_offset;
		logic MC0_dev_selected, MC0_mem_write_enable;
		assign MC0_error_bounds = wrapper.MC0.error_bounds;
		assign MC0_error_size = wrapper.MC0.error_size;
		assign MC0_error_no_idle = wrapper.MC0.error_no_idle;
		assign MC0_error_offset = wrapper.MC0.error_offset;
		assign MC0_dev_selected = wrapper.MC0.dev_selected;
		assign MC0_mem_write_enable = wrapper.MC0.mem_write_enable;
		
		// Memory Controller MC1
		logic MC1_error_bounds, MC1_error_size, MC1_error_no_idle, MC1_error_offset;
		logic MC1_dev_selected, MC1_mem_write_enable;
		assign MC1_error_bounds = wrapper.MC1.error_bounds;
		assign MC1_error_size = wrapper.MC1.error_size;
		assign MC1_error_no_idle = wrapper.MC1.error_no_idle;
		assign MC1_error_offset = wrapper.MC1.error_offset;
		assign MC1_dev_selected = wrapper.MC1.dev_selected;
		assign MC1_mem_write_enable = wrapper.MC1.mem_write_enable;
		 
	`endif
	

	// System Wide Signal Generation:
	logic HCLK;
	logic HRESETn;

	// Initalize clock and reset signals:
	initial begin
		HCLK = 0;
		HRESETn = 0;
		#CLOCK_PERIOD HRESETn = 1;								// delay by one clock cycle
	end
	
	// Start Clock:
	always #(CLOCK_PERIOD/2) HCLK = ~HCLK;

	// Module Instantiations:
	ahb_lite_bus AHB_Bus(.HCLK(HCLK), .HRESETn(HRESETn));			// Create AHB-Lite Interface
	ahb_lite_slave_wrapper wrapper(.bus_port_0(AHB_Bus.SLAVE0),
		.bus_port_1(AHB_Bus.SLAVE1));								// Create AHB-Lite Slaves and connect to ahb_interface
	ahb_lite_tb_interface tb_interface(.master(AHB_Bus.MASTER), 
		.slave(AHB_Bus.DUMMY_SLAVE));								// Create Testbench interface, pass Testbench Modports
	ahb_monitor	tb_monitor(AHB_Bus);								// Create and attach monitor to the AHB_Lite Bus
	ahb_lite_tb_sequencer tb_sequencer(tb_interface);				// Create an instance of the sequencer program

endmodule 
