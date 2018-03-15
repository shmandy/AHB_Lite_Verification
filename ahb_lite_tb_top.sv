//////////////////////////////////////////////////////////////
// ahb_lite_tb_top.sv - AHB-Lite Slave Testbench TOP module (driver) TBX MODE
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
//
// Description:
// ------------
// This is the top module for an AHB-LIte Testbench to run in Veloce TBX Mode
//
////////////////////////////////////////////////////////////////

import ahb_lite_defs::*; // Import package

module ahb_lite_tb_top();

	// Sequencer Insance:
	ahb_lite_tb_sequencer tb_sequencer(ahb_lite_dut_top.tb_interface);	// Create an instance of sequencer program
	
	// Assertion Insance (do we include this here?)
	// ahb_lite_monitor tb_monitor(AHB_Bus);							// Create and attach monitor to the AHB_Lite Bus

endmodule 
