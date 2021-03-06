//////////////////////////////////////////////////////////////
// ahb_lite_tb_top.sv - AHB-Lite Slave Testbench TOP module (driver)
//
// Authors: 
//	Andrew Elliott (andy@pdx.edu)
// 
// Date: 3/13/2018
// Version 0.1
//
//
// Revisions:
//
//
//
// Description:
// ------------
// This module contains the program for driving the test_bench
// 
// Data transactins are facilitated by the testbench Class
//
//
////////////////////////////////////////////////////////////////

import ahb_lite_defs::*; 				// Import Definitions Packages

//`define DISPLAY_DATA					// Enable Data Display // WARNING! Too much print data will cause QuestaSim to crash!
//`define STOP_ASSERTION				// Stop on assertion fail

// Driver Sequencer
// Generates input and executes testbench tasks
program ahb_lite_tb_sequencer(
	ahb_lite_tb_interface tb_interface
	);
	
	// Test Parameters
	parameter rw_loop_max = 100;					// Perform 100 Random Read-Write Operations
	parameter test_packets = 10;					// Array of test data packets
	parameter SEED = 2936483;						// Random Number Generator Seed
	
	// Test Variables:
	int random_data;
	int rw_index, index;							// read-write index, genral pupos index
	testdata_t tPacket [test_packets-1:0];			// Test data elements (class objects)
	testdata_t tIdlePacket;							// An Idle Packet
	testdata_bfm_t temp_bfm_input;					// Temp Input Packet (packed for BFM)
	
	// Configure Monitoring
	// Attach a monitor to every packet.
	`ifdef DISPLAY_DATA
		initial begin
			for(index = 0; index < test_packets; index++) begin
				$strobe($time, "\tPacket #: %d\t HADDR: %h\t HRDATA: %h\t HWDATA: %h\t HSIZE: %s\t HBURST: %s\t HTRANS: %s\t HREADY: %s\t HRESP: %s\n\n", 
					index, tPacket[index].address, tPacket[index].data_in, tPacket[index].data_out, tPacket[index].HSIZE.name(), tPacket[index].HBURST.name(), 
					tPacket[index].HTRANS.name(), tPacket[index].HREADY.name(), tPacket[index].HRESP.name());
			end
		end
	`endif
	
	
	// Simple read-write Test Loop
	// Using only SINGLE Write
	// Does not use sequence
	// SIZE and 
	initial begin
		
		//  $srandom(SEED);				// Seed RNG
		//  $urandom_range(SIZE, 0)		// RNG TEMPLATE
		
		// Initialize Test Packets:
		tIdlePacket = new();
		tIdlePacket.HTRANS = IDLE;
		tIdlePacket.address = { SLAVE0_ADDR, 24'b0 };			// Set to Slave 1
		
		for(index = 0; index < test_packets; index++) begin
			tPacket[index] = new();								// Initialize Packet
			tPacket[index].rand_mode(1);						// Enable Randomization Calls
			assert( tPacket[index].randomize() );				// Assert Randomize data objects
			tPacket[index].setRandom(.constrain_range(1));		// Select Slave and Constrained location at random
		end
		
		
		// Send IDLE packet (delay on bus)
		tb_interface.single_read(tIdlePacket);
		tb_interface.wait_cycle();								// Wait one clock edge
		
		// Write_Then_Read Loop:
		for(rw_index = 0; rw_index < rw_loop_max; rw_index++) begin
			
			// Write packet to device, then read it back
			for(index = 0; index < test_packets; index ++) begin
				tb_interface.single_trx(tPacket[index].getBfmPacket(), temp_bfm_input);
				tPacket[index].bfm_copy_from(temp_bfm_input);	// Copy returned packed structure into class object
				check_error(tPacket[index]);
			end
			
			// Read packets back and validate:
			for(index = 0; index < test_packets; index ++) begin
				tb_interface.single_trx(tPacket[index].getBfmPacket(), temp_bfm_input);
				tPacket[index].bfm_copy_from(temp_bfm_input);	// Copy returned packed structure into class object
				single_read_valid: assert(tPacket[index].compare());
				check_error(tPacket[index]);
			end
			
			// Reset Test Data:
			for(index = 0; index < test_packets; index++) begin
				tPacket[index].setRandom(.constrain_range(1));	// Enable randomization
				assert( tPacket[index].randomize() );			// Assert Randomize data objects
			end
			
			// Send IDLE packet (delay on bus)
			tb_interface.single_trx(tIdlePacket.getBfmPacket());
			tb_interface.wait_cycle();							// Wait Before Next Round
			
		end // END Read-Write Loop
		$stop; // End Simulation
	end  
	
	
	// If an Error Response is generated
	// Set an IDLE flag and wait one cycle before resuming test.
	task automatic check_error(
		ref testdata_t pkt
		);
		begin
			if(pkt.HRESP == ERROR) begin
				tIdlePacket.copy_from(pkt);
				tIdlePacket.HTRANS = IDLE;
				tb_interface.single_trx(tIdlePacket.getBfmPacket());
			end
		end
	endtask: check_error
  
endprogram 