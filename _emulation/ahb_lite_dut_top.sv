//////////////////////////////////////////////////////////////
// ahb_lite_dut_top.sv - AHB-Lite Slave TOP module for Veloce TBX emulation
//
// Author:
// Andrew Elliott (andy@pdx.edu)
// 
// Date: 3/14/2018
// Version 0.1
//
//
// Revisions:
//
// Description:
// ------------
// This is the top module for the AHB-Lite Slave DUT
// TBX - Emulated Module
// Ports exposed to test bench via pragmas
//
// Contains "clockgen" statements
// Exposes DUT via partition_module_xrtl 
//
////////////////////////////////////////////////////////////////

// Veloce Emulation - DUT TOP FILE
// Requrires pragmas to expose pins.
module ahb_lite_dut_top;

	prameter CLOCK_DC = 5;		// Internally-generated clock duty-cycle (1/2 period)

	// DUT TOP PRAGMA:
	//pragma attribute ahb_lite_dut_top partition_module_xrtl
	
	// Clock and Reset
	bit HCLK;
	bit HRESETn;
	
	// AHB-Lite Bus (access signals from here)
	ahb_lite_bus AHB_Bus(.*);
	
	// DUT Insance:
	ahb_lite_slave_wrapper(
		.bus_port_0(AHB_Bus.SLAVE0),
		.bus_port_1(AHB_Bus.SLAVE1)
		);
	
	// Test Bench Interface (Driver)
	ahb_lite_tb_interface tb_interface(
		.master(AHB_Bus.MASTER),
		.slave(AHB_BUs.DUMMY_SLAVE)
		);


	// Start Clock:
	// tbx clkgen
	initial begin
		HCLK = 0;
		forever begin
			#CLOCK_DC HCLK = ~HCLK;
		end
	end
	
	// Configure Reset
	//tbx clkgen
	initial begin
		HRESETn = 0;
		#CLOCK_DC HRESETn = 1;
	end

endmodule: ahb_lite_dut_top