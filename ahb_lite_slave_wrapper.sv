//////////////////////////////////////////////////////////////
// ahb_lite_slave_wrapper.sv - AHB-Lite Dual-port memory controller
//
// Author: Andrew Elliott (andy@pdx.edu)
// Date: 3/9/2018
//
// Version 0.2
//
//
// Revisions:
// QuestSim issue with passed-in parameters?
//
// Description:
// ------------
// This is a wrapper module for splitting memory access of a dual-port RAM module
// between two instances of the memory controller.
////////////////////////////////////////////////////////////////

import ahb_lite_defs::*; // Import package

module ahb_lite_slave_wrapper(
	ahb_lite_bus.SLAVE0 bus_port_0,				// Mapped to MC0 / Port A
	ahb_lite_bus.SLAVE1 bus_port_1				// Mapped to MC1 / Port B
);
	
	// DP RAM Connections:
	logic we_a, we_b;
	logic [ADDRWIDTH-1:0] addr_a, addr_b;
	logic [DATAWIDTH-1:0] data_a, data_b, q_a, q_b;

	// Memory Module:
	// Signals marked 'managed' require interaction from memory controller.
	dual_port_RAM RAM0(
		.q_a(q_a),				// Data out A
		.q_b(q_b),				// Data out B
		.clk_a(bus_port_0.HCLK),	// Clock A
		.clk_b(bus_port_1.HCLK),	// Clock B
		.addr_a(addr_a),			// Address A (managed)
		.addr_b(addr_b),			// Address B (managed)
		.data_a(data_a),			// Data in A
		.data_b(data_b),			// Data in B
		.we_a(we_a),				// Write enable A (managed)
		.we_b(we_b),				// Write enable B (managed)
		.size_a(bus_port_0.HSIZE),	// Size Select
		.size_b(bus_port_1.HSIZE)	// Size Select
	);
	
	// Memory Controller 0
	ahb_lite_mem_ctrl #(SLAVE0_SEL) MC0(
		// AHB-Lite Interface:
		.HREADYOUT(bus_port_0.HREADYOUT0),	// ReadyOut
		.HRESP(bus_port_0.HRESP0),			// Response Out
		.HRDATA(bus_port_0.HRDATA0),		// Data Out (read)
		.HCLK(bus_port_0.HCLK),				// Clock
		.HRESETn(bus_port_0.HRESETn),		// Rest_n
		.HADDR(bus_port_0.HADDR),			// Address
		.HTRANS(bus_port_0.HTRANS),			// Transfer Type
		.HSIZE(bus_port_0.HSIZE),			// Transfer Size
		.HBURST(bus_port_0.HBURST),			// Transfer Burst Type
		.HWDATA(bus_port_0.HWDATA),			// Data In (write)
		.HWRITE(bus_port_0.HWRITE),			// Write-enable signal
		.HSEL(bus_port_0.HSEL),				// HSEL signal (device select)
		// Dual-port Ram (port A):
		.mem_address(addr_a),				// DP RAM Address
		.mem_data_in(data_a),				// DP RAM Data Input (write)
		.mem_write_enable(we_a),			// DP RAM Write Enable
		.mem_data_out(q_a)					// DP RAM Data Output (read)
	);
	
	// Memory Controller 1
	ahb_lite_mem_ctrl #(SLAVE1_SEL) MC1(
		// AHB-Lite Interface:
		.HREADYOUT(bus_port_1.HREADYOUT1),
		.HRESP(bus_port_1.HRESP1),
		.HRDATA(bus_port_1.HRDATA1),
		.HCLK(bus_port_1.HCLK),
		.HRESETn(bus_port_1.HRESETn),
		.HADDR(bus_port_1.HADDR),
		.HTRANS(bus_port_1.HTRANS),
		.HBURST(bus_port_1.HBURST),
		.HSIZE(bus_port_1.HSIZE),
		.HWDATA(bus_port_1.HWDATA),
		.HWRITE(bus_port_1.HWRITE),
		.HSEL(bus_port_1.HSEL),
		// Dual-port Ram (port B):
		.mem_address(addr_b),
		.mem_data_in(data_b),
		.mem_write_enable(we_b),
		.mem_data_out(q_b)
	);
	
endmodule: ahb_lite_slave_wrapper