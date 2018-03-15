//////////////////////////////////////////////////////////////
// ahb_lite_bus.sv - An AHB-Lite Interface
//
// Author: Andrew Elliott (andy@pdx.edu)
// Date: 3/5/2018
//
// Version 0.2
//
//
// Revisions:
//
//	3/12 Minor Fixes to signals
//
//
// Description:
// ------------
// This AHB-Lite interface is designed for use between an AHB-Lite bust master
// and a two slave devices (peripheral)
// Note: 32-bit Implementation
////////////////////////////////////////////////////////////////

import ahb_lite_defs::*; // Import package

// Interface:
interface ahb_lite_bus(
	input HCLK,									// Bus Clock
	input HRESETn									// Active-low Reset
	);
	
	// Transfer Signals
	hready_t HREADY;								// Previous Transfer is Completed (to all)
	hready_t HREADYOUT0, HREADYOUT1, HREADYOUT2, 
		HREADYOUTD;								// HIGH signals transfer has finished on the bus. Signal LOW to extend transfer.
	hresp_t HRESP, HRESP0, HRESP1, HRESPD;						// LOW signals transfer status is OK, HIGH signals an ERROR on the bus (slave).
	logic [2:0] HSEL;								// Device Selection Bits
	logic [2:0] HSEL_d;								// Synchronized Select Signal
	hwrite_t HWRITE;								// LOW indicates a read, HIGH indicates a write.
	
	// Control Signals
	hsize_t HSIZE;									// Size of the transfer: byte, halfword or word. Up to 1024bits
	hburst_t HBURST;								// 4, 8, or 16 beats. Incremented or Wrapping
	logic [3:0] HPROT;								// Protection control signals (not used)
	htrans_t HTRANS;								// State of current transfer: IDLE, BUSY, NONSEQUENTIAL, SEQUENTIAL
	logic HMASTLOCK;								// HIGH indicates transfer is part of a locked sequence.
	
	// Bus Ports:
	logic [AHB_ADDRWIDTH-1:0] HADDR;						// Address  (from master)
	logic [AHB_DATAWIDTH-1:0] HRDATA, HRDATA0, HRDATA1, HRDATAD;  			// Read Data (to master)
	logic [AHB_DATAWIDTH-1:0] HWDATA;						// Write Data (from master)
	
	// Bus Master modport (single instance only)
	modport MASTER(
		output HADDR, HWRITE, HSIZE, HBURST, HPROT, HTRANS, HMASTLOCK, HWDATA,
		input HCLK, HRESETn, HREADY, HRESP, HRDATA
	);
	
	// Bus Slave 0 modport (single instance only)
	// Must set SELECT for each instance.
	modport SLAVE0(
		output HREADYOUT0, HRESP0, HRDATA0,
		input HCLK, HRESETn, HSEL, HADDR, HWRITE, HSIZE, HBURST, HPROT, HTRANS, HMASTLOCK, HREADY, HWDATA
	);


	// Bus Slave 1 modport (single instance only)
	// Must set SELECT for each instance.
	modport SLAVE1(
		output HREADYOUT1, HRESP1, HRDATA1,
		input HCLK, HRESETn, HSEL, HADDR, HWRITE, HSIZE, HBURST, HPROT, HTRANS, HMASTLOCK, HREADY, HWDATA
	);	
	
	// Bus Slave 3 modport (single instance only)
	// Dummy - used for testing
	// Must set SELECT for each instance
	modport DUMMY_SLAVE(
		output HREADYOUTD, HRESPD, HRDATAD,
		input HCLK, HRESETn, HSEL, HADDR, HWRITE, HSIZE, HBURST, HPROT, HTRANS, HMASTLOCK, HREADY, HWDATA
	);	
	
	
	///////////////
	// Bus Logic //
	///////////////
	
	// Bus Address Selection:
	// Use Address to determine which slave is currently active:
	// Configure address scheme here...
	assign HSEL[0] = (HADDR[31:24] == SLAVE0_ADDR);	
	assign HSEL[1] = (HADDR[31:24] == SLAVE1_ADDR);	
	assign HSEL[2] = (HADDR[31:24] == DUMMYSLAVE_ADDR);
	

	// Bus Output Multiplexer:
	// Select which slave is writing to the master.
	// Note this is held by one clock cycle (HSEL_d)
	
	// Align HSEL Signal with Clock:
	// This forces a 1-cycle delay on the output MUX
	always_ff @(posedge HCLK) begin
		HSEL_d <= HSEL;
	end	
	
	always_comb begin
		casez(HSEL_d)
			3'b??1:	// Select Slave 0
				begin
					HRDATA = HRDATA0;		// Select Data
					HRESP = HRESP0;			// Select Response
					HREADY = HREADYOUT0;		// Select Ready
				end
				
			3'b?10:	// Select Slave 1
				begin
					HRDATA = HRDATA1;	
					HRESP = HRESP1;
					HREADY = HREADYOUT1;
				end
				
			3'b100: // Select Dummy
				begin
					HRDATA = HRDATAD;	
					HRESP = HRESPD;
					HREADY = HREADYOUTD;
				end
				
			default:	// Select Dummy
				begin
					HRDATA = HRDATAD;	
					HRESP = HRESPD;
					HREADY = HREADYOUTD;
				end
		endcase
	end
	
	
endinterface: ahb_lite_bus