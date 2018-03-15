//////////////////////////////////////////////////////////////
// ahb_lite_mem_ctrl.sv - AHB-Lite Dual-port memory controller
//
// Author: Andrew Elliott (andy@pdx.edu)
// Date: 3/5/2018
//
// Version 0.2
//
//
// Revisions:
// 3/9: Changed signals to typedefs (from ahb_lite_defs)
//
//
// Description:
// ------------
// This AHB-Lite memory controller module is used to drive a single dual-port
// memory module with two AHB-Lite Slave interfaces.
////////////////////////////////////////////////////////////////


import ahb_lite_defs::*; // Import package

module ahb_lite_mem_ctrl#( parameter SEL_SIG = 3'h0) ( 

	// AHB-Lite Interface Signals:
	output hready_t HREADYOUT,					// Ready Signal (wait states)
	output hresp_t HRESP,						// Transfer status HIGH = ERROR
	output logic [AHB_DATAWIDTH-1:0] HRDATA, 	// Data Bus Out
	input logic HCLK,							// Bus Clock
	input logic HRESETn,						// Bus Reset (Active Low)
	input logic [AHB_ADDRWIDTH-1:0] HADDR,		// Address
	input htrans_t HTRANS,						// Transfer Type (enum)
	input hsize_t HSIZE,						// Transfer Size (enum)
	input hburst_t HBURST,						// Transfer Burst Type (enum)
	input logic [AHB_DATAWIDTH-1:0] HWDATA,		// Data Bus In
	input hwrite_t HWRITE,						// Write Enable
	input logic [2:0] HSEL,		// Select
	
	// RAM Interface Signals
	output logic [ADDRWIDTH-1:0] mem_address,	// Memory Address for RAM
	output logic [DATAWIDTH-1:0] mem_data_in,	// Data to RAM
	output logic mem_write_enable,				// Write Enable
	input logic [DATAWIDTH-1:0] mem_data_out		// Data from RAM
);


	// Device Enable:
	logic dev_selected;													// Device enabled signal
	assign dev_selected = (HSEL == SEL_SIG);							// Enable when selected
	assign mem_address = (dev_selected) ? HADDR[ADDRWIDTH-1:0] : '0;	// Pass-thru address when enabled
	
	// Read Control:
	//assign HRDATA = (dev_selected && ~HRESP) ? mem_data_out : '0;		// Output bus mux
	assign HRDATA = mem_data_out;		
	
	// Read Control:
	assign mem_write_enable = ( dev_selected && HWRITE == WRITE );		// Write Enabled Signal
	assign mem_data_in = (mem_write_enable) ? HWDATA : '0;				// Input bus Mux
	
	// Error Signals
	logic error_bounds, error_size, error_no_idle, error_offset;		// Error Signals (comb)
	htrans_t prev_htrans;												// Previous HTRANS type 
	
	assign error_size = (dev_selected && HSIZE > WORD) ? 1'b1 : 1'b0;					// Bad Size Select
	assign error_bounds = (dev_selected && HADDR[23:ADDRWIDTH] > 1) ? 1'b1 : 1'b0;		// Out-of-bounds address
	assign error_no_idle = (dev_selected && HTRANS == SEQ && prev_htrans != NONSEQ);	// Bad State Transition
	
	// Offset Error Detection:
	always_comb begin
		if(dev_selected) begin
			if(HSIZE == WORD && HADDR[1:0] > 2'b00)						// No Offset for Words
				error_offset = 1'b1;
			else if (HSIZE == HALFWORD && (HADDR[1:0] == 2'b01) || (HADDR[1:0] == 2'b11)) // Offset of 1 or 3 on Halfword		
				error_offset = 1'b1;
			else
				error_offset = 1'b0;
			end
		else 	error_offset = 1'b0;
	end
	

	// Device Control Signals:
	always_ff @(posedge HCLK, negedge HRESETn) begin
		
		// Reset System
		if(!HRESETn) begin
			HRESP <= OKAY;			// Set response to OKAY
			HREADYOUT <= READY;		// Set ready to FINSIHED
			prev_htrans <= IDLE;		// Set to IDLE
		end
		
		
		else begin
			
			// Get Transition Type (delay by one clock)
			prev_htrans <= HTRANS;
		
			// Device Enabled
			if(dev_selected) begin
				
				// Reset Responses
				if( HTRANS == IDLE ) begin
					HRESP <= OKAY;
					HREADYOUT <= READY;
				end
				else begin
				
					// Check for Errors
					if(error_bounds || error_no_idle || error_offset || error_size)
						HRESP <= ERROR;
					else
						HRESP <= HRESP;
					
					// Generate Wait State
					if( HTRANS == NONSEQ && HBURST != SINGLE)
						HREADYOUT <= WAIT;
					else
						HREADYOUT <= READY;
				end

			end
			
			// Device Disabled
			else begin
				HRESP <= OKAY;
				HREADYOUT <= READY;
			end
		end
	end


	
endmodule: ahb_lite_mem_ctrl