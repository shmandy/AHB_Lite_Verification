//////////////////////////////////////////////////////////////
// ahb_lite_tb_top.sv - AHB-Lite Slave Testbench TOP module (driver)
//
// Authors: 
//	Andrew Elliott (andy@pdx.edu)
//	Mohamed Abibalrekab 
// 
// Date: 3/13/2018
// Version 0.2
//
//
// Revisions:
// 3/14 Added Example Sequential Write
// 3/15
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
	
	// Test Variables:
	int random_data, base_address;
	int rw_index, index;							// read-write index, genral pupos index
	testdata_t tPacket [test_packets-1:0];			// Test data elements (class objects)
	testdata_t tIdlePacket;							// An Idle Packet
	logic [31:0] address_wrap;						// Wrapping Address
	int idx;										// Beats in burst
	int isize;										// HSIZE control
	
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
		
		
		/////////////////////////////////////////////////////
		//			Single READ and WRITE testing		 //
		/////////////////////////////////////////////////////
		
		// Initialize Test Packets:
		tIdlePacket = new();
		tIdlePacket.HTRANS = IDLE;
		tIdlePacket.address = { SLAVE0_ADDR, 24'b0 };			// Set to Slave 1
		
		for(index = 0; index < test_packets; index++) begin
			tPacket[index] = new();								// Initialize Packet
			assert( tPacket[index].randomize() );				// Assert Randomize data objects
			tPacket[index].rand_mode(1);						// Enable Randomization Calls
			tPacket[index].setRandom(.constrain_range(1));		// Select Slave and Constrained location at random
		end
		
		
		// Send IDLE packet (delay on bus)
		tb_interface.single_read(tIdlePacket);
		
		tb_interface.wait_cycle();	// Wait One Cycle
		
		// Write_Then_Read Loop:
		for(rw_index = 0; rw_index < rw_loop_max; rw_index++) begin
			
			// Write packet to device, then read it back
			for(index = 0; index < test_packets; index ++) begin
				tb_interface.single_write(tPacket[index]);
				check_error(tPacket[index]);
			end
			
			// Read packets back and validate:
			for(index = 0; index < test_packets; index ++) begin
				tb_interface.single_read(tPacket[index]);
				single_read_valid: assert(tPacket[index].compare());
				check_error(tPacket[index]);
			end
			
			// Reset Test Data:
			for(index = 0; index < test_packets; index++) begin
				assert( tPacket[index].randomize() );		// Assert Randomize data objects
				tPacket[index].setRandom(.constrain_range(1));														// Select Slave and Location at random
			end
			
			// Send IDLE packet (delay on bus)
			tb_interface.single_read(tIdlePacket);
			
			tb_interface.wait_cycle();	// Wait One Cycle
			
		end // END Read-Write Loop
		
		
		/////////////////////////////////////////////////////
		//	 INCR WRITE Test			  // 
		/////////////////////////////////////////////////////
		
		
		
		// Single Write Sequnce Loop
		// Setup Packets
		for(index = 0; index < test_packets; index++) begin
		
			// "Clean Up" current packets:
			tPacket[index].rand_mode(1);						// Enable Randomization Calls
			assert( tPacket[index].randomize() );				// Assert Randomize data objects
			tPacket[index].setRandom(.constrain_range(1));		// Select Slave and Constrained location at random
			
			// Setup Write Packets for INCR test:
			if(0 == index) begin
				tPacket[index].address = { tPacket[index].address[31:2], 2'b00 };	// Set correct offset
				base_address = tPacket[index].address;	// Get base address (first packet)
				tPacket[index].HTRANS = NONSEQ;			// Set first in seq. to NONSEQ
			end
			else begin	// Set remaining packets:
				tPacket[index].HTRANS = SEQ;						// Set to SEQUENCE mode
				tPacket[index].address = base_address + (index * 4);	// Set Incrementing addresses (WORD)
			end
			
			tPacket[index].HBURST = INCR;						// Set all packets to INCREMENT Burst
			tPacket[index].HSIZE = WORD;						// Set all packets to WORD size
			tPacket[index].HWRITE = WRITE;						// Set all to WRITE
			
		end
		
		// Write packets to interface
		// Read responses to check for possible error conditions
		for(index = 0; index < test_packets; index++) begin
			tb_interface.half_trx(tPacket[index]);
			seq_check_error: assert(tPacket[index].HRESP != ERROR) break;	// Break loop if error occures on bus
		end
		
		// Send IDLE packet (delay on bus)
		tb_interface.single_read(tIdlePacket);
		
		//.................................................................................................................//	
		//.................................................................................................................//
		//....................................  INCR 4, 8 , 16 ...... WRITE & READ ....................... ................//
		//.................................................................................................................//
			// Single Write Sequnce Loop
			// Setup Packets
	   for (idx = 4; idx <= 16; idx = idx *2) begin 
			  for (isize = 1; isize <= 4; isize = isize*2) begin
				  for( index = 0; index <= idx - 1; index ++) begin
			
					 // "Clean Up" current packets:
					 //tPacket[index].rand_mode(1);						// Enable Randomization Calls
					 assert( tPacket[index].randomize() );				// Assert Randomize data objects
					 tPacket[index].setRandom(.constrain_range(1));		// Select Slave and Constrained location at random
				
					 // Setup Write Packets for INCR test:
					 if(0 == index) begin
						  tPacket[index].address = { tPacket[index].address[31:2], 2'b00 };	// Set correct offset
						  base_address = tPacket[index].address;	// Get base address (first packet)
						  tPacket[index].HTRANS = NONSEQ;			// Set first in seq. to NONSEQ
					 end
					 else begin	// Set remaining packets:
						  tPacket[index].HTRANS = SEQ;						// Set to SEQUENCE mode
						  tPacket[index].address = base_address + (index * isize);	// Set Incrementing addresses (WORD)
					 end
					 if (idx == 4)
						tPacket[index].HBURST = INCR4;      // Set all packets to INCREMENT 4 Burst
					 else if (idx == 8) 
						tPacket[index].HBURST = INCR8;						// Set all packets to INCREMENT 8 Burst
					 else if (idx == 16)
						tPacket[index].HBURST = INCR16;     // Set all packets to INCREMENT 16 Burst
				
					 if (isize == 1)
					   tPacket[index].HSIZE = BYTE;						      // Set all packets to BYTE size
					 else if (isize == 2)
					   tPacket[index].HSIZE = HALFWORD;						// Set all packets to HALFWORD size
				   else if (isize == 4)
					tPacket[index].HSIZE = WORD;					   	// Set all packets to WORD size
				
					 tPacket[index].HWRITE = WRITE;						// Set all to WRITE
				
				   end
				  // Write packets to interface
				  // Read responses to check for possible error conditions
				  for(index = 0; index < idx -1; index++) begin
					   tb_interface.half_trx(tPacket[index]);
					   seq_check_error1: assert(tPacket[index].HRESP != ERROR) break;	// Break loop if error occures on bus
				  end
				  // Send IDLE packet (delay on bus)
				  tb_interface.single_read(tIdlePacket);
				  
			   end
			end
			
		//........................................................Burst wrapping addresses.........................................//
							 // test case when we have 4 beat                   
		
		for( index = 0; index <= 3; index ++) begin
				  isize = 4;   // we have Hsize = a word.
					 // "Clean Up" current packets:
					 //tPacket[index].rand_mode(1);						// Enable Randomization Calls
					 assert( tPacket[index].randomize() );				// Assert Randomize data objects
					 tPacket[index].setRandom(.constrain_range(1));		// Select Slave and Constrained location at random
				
					 // Setup Write Packets for INCR test:
					 if(index == 0) begin
						  tPacket[index].address = { tPacket[index].address[31:2], 2'b00 };	// Set correct offset
						  base_address = tPacket[index].address;	// Get base address (first packet)
						  address_wrap = base_address;
						  tPacket[index].HTRANS = NONSEQ;			// Set first in seq. to NONSEQ
					 end
					 else begin	// Set remaining packets:
						  tPacket[index].HTRANS = SEQ;						// Set to SEQUENCE mode
						  address_wrap = wrap(base_address, index, isize);  // call a function to wrap the address if it excess the limit. 
						  tPacket[index].address = address_wrap;	       // Set Incrementing addresses (WORD)
					 end
					 if (idx == 4)
						tPacket[index].HBURST = INCR4;      // Set all packets to INCREMENT 4 Burst
					 else if (idx == 8) 
						tPacket[index].HBURST = INCR8;						// Set all packets to INCREMENT 8 Burst
					 else if (idx == 16)
						tPacket[index].HBURST = INCR16;     // Set all packets to INCREMENT 16 Burst
				
					 if (isize == 1)
					   tPacket[index].HSIZE = BYTE;						      // Set all packets to BYTE size
					 else if (isize == 2)
					   tPacket[index].HSIZE = HALFWORD;						// Set all packets to HALFWORD size
				   else if (isize == 4)
					tPacket[index].HSIZE = WORD;					   	// Set all packets to WORD size
				
					 tPacket[index].HWRITE = WRITE;						// Set all to WRITE
				
				   end
				  // Write packets to interface
				  // Read responses to check for possible error conditions
				  for(index = 0; index < idx -1; index++) begin
					   tb_interface.half_trx(tPacket[index]);
					   seq_check_error2: assert(tPacket[index].HRESP != ERROR) break;	// Break loop if error occures on bus
				  end
				  // Send IDLE packet (delay on bus)
				  tb_interface.single_read(tIdlePacket);
				  
				  //--------------------------------------------- wrap 8 ------------------------------------------------------//
				  for( index = 0; index <= 7; index ++) begin     // 8 beaats
				  isize = 4;   // we have Hsize = a word.
					 // "Clean Up" current packets:
					 //tPacket[index].rand_mode(1);						// Enable Randomization Calls
					 assert( tPacket[index].randomize() );				// Assert Randomize data objects
					 tPacket[index].setRandom(.constrain_range(1));		// Select Slave and Constrained location at random
				
					 // Setup Write Packets for INCR test:
					 if(index == 0) begin
						  tPacket[index].address = { tPacket[index].address[31:2], 2'b00 };	// Set correct offset
						  base_address = tPacket[index].address;	// Get base address (first packet)
						  address_wrap = base_address;
						  tPacket[index].HTRANS = NONSEQ;			// Set first in seq. to NONSEQ
					 end
					 else begin	// Set remaining packets:
						  tPacket[index].HTRANS = SEQ;						// Set to SEQUENCE mode
						  address_wrap = wrap(base_address, index, isize);  // call a function to wrap the address if it excess the limit. 
						  tPacket[index].address = address_wrap;	       // Set Incrementing addresses (WORD)
					 end
					 if (idx == 4)
						tPacket[index].HBURST = INCR4;      // Set all packets to INCREMENT 4 Burst
					 else if (idx == 8) 
						tPacket[index].HBURST = INCR8;						// Set all packets to INCREMENT 8 Burst
					 else if (idx == 16)
						tPacket[index].HBURST = INCR16;     // Set all packets to INCREMENT 16 Burst
				
					 if (isize == 1)
					   tPacket[index].HSIZE = BYTE;						      // Set all packets to BYTE size
					 else if (isize == 2)
					   tPacket[index].HSIZE = HALFWORD;						// Set all packets to HALFWORD size
				   else if (isize == 4)
					tPacket[index].HSIZE = WORD;					   	// Set all packets to WORD size
				
					 tPacket[index].HWRITE = WRITE;						// Set all to WRITE
				
				   end
				  // Write packets to interface
				  // Read responses to check for possible error conditions
				  for(index = 0; index < idx -1; index++) begin
					   tb_interface.half_trx(tPacket[index]);
					   seq_check_error3: assert(tPacket[index].HRESP != ERROR) break;	// Break loop if error occures on bus
				  end
				  // Send IDLE packet (delay on bus)
				  tb_interface.single_read(tIdlePacket);
				 //--------------------------------------------- wrap 16 ------------------------------------------------------//
				 for( index = 0; index <= 15; index ++) begin     // 16 beaats
				  isize = 4;   // we have Hsize = a word.
					 // "Clean Up" current packets:
					 //tPacket[index].rand_mode(1);						// Enable Randomization Calls
					 assert( tPacket[index].randomize() );				// Assert Randomize data objects
					 tPacket[index].setRandom(.constrain_range(1));		// Select Slave and Constrained location at random
				
					 // Setup Write Packets for INCR test:
					 if(index == 0) begin
						  tPacket[index].address = { tPacket[index].address[31:2], 2'b00 };	// Set correct offset
						  base_address = tPacket[index].address;	// Get base address (first packet)
						  address_wrap = base_address;
						  tPacket[index].HTRANS = NONSEQ;			// Set first in seq. to NONSEQ
					 end
					 else begin	// Set remaining packets:
						  tPacket[index].HTRANS = SEQ;						// Set to SEQUENCE mode
						  address_wrap = wrap(base_address, index, isize);  // call a function to wrap the address if it excess the limit. 
						  tPacket[index].address = address_wrap;	       // Set Incrementing addresses (WORD)
					 end
					 if (idx == 4)
						tPacket[index].HBURST = INCR4;      // Set all packets to INCREMENT 4 Burst
					 else if (idx == 8) 
						tPacket[index].HBURST = INCR8;						// Set all packets to INCREMENT 8 Burst
					 else if (idx == 16)
						tPacket[index].HBURST = INCR16;     // Set all packets to INCREMENT 16 Burst
				
					 if (isize == 1)
					   tPacket[index].HSIZE = BYTE;						      // Set all packets to BYTE size
					 else if (isize == 2)
					   tPacket[index].HSIZE = HALFWORD;						// Set all packets to HALFWORD size
				   else if (isize == 4)
					tPacket[index].HSIZE = WORD;					   	// Set all packets to WORD size
				
					 tPacket[index].HWRITE = WRITE;						// Set all to WRITE
				
				   end
				  // Write packets to interface
				  // Read responses to check for possible error conditions
				  for(index = 0; index < idx -1; index++) begin
					   tb_interface.half_trx(tPacket[index]);
					   seq_check_error4: assert(tPacket[index].HRESP != ERROR) break;	// Break loop if error occures on bus
				  end
				  
				  
				  // Send IDLE packet (delay on bus)
				  tb_interface.single_read(tIdlePacket);
				  /////////////////////////////////////////////////////////// Tests Ends here//////////////////////////////////////

		
		$finish;	// End Simulation

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
				tb_interface.single_trx(tIdlePacket);
			end
		end
	endtask: check_error
	
	 // Wrapping Function (for any size)
	function automatic wrap(
		input logic [31:0] base_address,
		input int index, 
		input int isize
		);
		
		logic [31:0] wrap_t;
		if (base_address[3:0] + index * isize > 15)
			wrap_t[31:4] = base_address[31:4];
		else
			wrap_t = base_address + index * isize;
		wrap = wrap_t;
	endfunction
  
endprogram 