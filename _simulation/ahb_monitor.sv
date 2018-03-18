/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// ahb_monitor.sv - AHB-Lite Monitor and Scoreboard 
//
// Author:Snehasri Nag(snehasri@pdx.edu)
// Date: 3/14/2018
//
// Version 0.1
//
// Description:
// ------------
// This is the assertion module for an AHB-LIte 
// This module checks the design at the signal level and  displays the results accordingly.
// The scoreboard is displayed at the end with all the values of the success and failures of the assertions
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////






module ahb_monitor(ahb_lite_bus bus);


///////////////////////Counters for keeping the rack of the score for number of failures and success/////////////////////////
int basic_write_transfer_pass;
int basic_write_transfer_fail;
int basic_read_transfer_pass;
int basic_read_transfer_fail;
int hready_chk_pass;
int hready_chk_fail;
int burst_read_pass;
int burst_read_fail;
int burst_write_pass;
int burst_write_fail;


parameter n=3; //n= number of slaves



// The below property checks whether the basic write function happens properly or not
// At the positive edge of the clock, when write signal from the master goes high and ready signal received by the master is high,
//then at the next positive edge of the clock, data to be written to the memory should be present on the data bus
property basic_write_transfer;
@(posedge bus.HCLK)disable iff(!bus.HRESETn)
(bus.MASTER.HWRITE && bus.MASTER.HREADY)|->##1 ($isunknown(bus.MASTER.HWDATA)!=1);
   endproperty


//Assertion of basic write property
assert property (basic_write_transfer)
basic_write_transfer_pass++;
else 
begin
basic_write_transfer_fail++;
end

// The below property checks whether the basic read function happens properly or not
// At the positive edge of the clock, when write signal from the master goes low and ready signal received by the master is high,
//then at the next positive edge of the clock, data to be read from the memory should be present on the data bus
property basic_read_transfer;
@(posedge bus.HCLK)disable iff(!bus.HRESETn)
(!bus.MASTER.HWRITE && bus.MASTER.HREADY)|->##1 ($isunknown(bus.MASTER.HRDATA)!=1);
   endproperty

//Assertion of basic read property
assert property (basic_read_transfer)
basic_read_transfer_pass++;
else 
begin
basic_read_transfer_fail++;
end

//The below property checks whether HREADY signal is serving its purpose in the design or not.
//If at the positive edge of the clock, HREADY received by master is low then in the next positive edge of the clock,
//HADDR and HWRITE and HWDATA should remain in the same state until it HREADY goes high.
property HREADY_check;
@(posedge bus.HCLK) (bus.MASTER.HREADY == 1'b0) |=> $stable (bus.MASTER.HADDR && bus.MASTER.HWRITE && bus.MASTER.HWDATA) ;
endproperty


//Assertion of HREADY check property
assert property (HREADY_check)
hready_chk_pass++;
else 
hready_chk_fail++;


// This property checks for the burst read.If HWRITE from the master is low & HTRANS from the master is in non sequential state at 2nd positive edge of the
//clock,then at the third positive edge of the clock,HREADY to master goes high.
property burst_read;
@(posedge bus.HCLK)
disable iff (bus.HTRANS == BUSY || (bus.MASTER.HADDR > ((2**10)* n)))
((bus.MASTER.HWRITE=='0)&&(bus.MASTER.HTRANS == 2'b10) )|=>(bus.MASTER.HREADY=='1) ;
endproperty	


//Assertion of basic burst read property
assert property(burst_read)
burst_read_pass++;
else
burst_read_fail++;

// This property checks for the basic  burst write  
//If HWRITE from the master is high in the positive edge of the clock and
//HTRANS is in non sequential state at the next positive edge of the clock,then at the third positive edge of the  clock,
//HREADY to the master goes high. This property is disabled if HTRANS from the master is busy
property burst_write;
@(posedge bus.HCLK)
disable iff (bus.MASTER.HTRANS == BUSY)
((bus.MASTER.HWRITE==1)&&(bus.MASTER.HTRANS == 2'b10) )|=>(bus.MASTER.HREADY=='1) ;
endproperty


//Assertion of basic burst write property
assert property (burst_write)
burst_write_pass++;
else
burst_write_fail++;


///////////////////////////////SCOREBOARD FOR ASSERTION///////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////All the assertions are are checked for and the score  relevant to the particular assertion has been displayed////////////

final
begin
$display("No of basic write transfer failures:%0d",basic_write_transfer_pass);
$display("No of basic write transfer success:%0d",basic_write_transfer_fail);
$display("No of basic read transfer failures:%0d",basic_read_transfer_pass);
$display("No of basic read transfer success:%0d",basic_read_transfer_fail);
$display("No of hready_check failures:%0d",hready_chk_fail);
$display("No of hready_check success:%0d",hready_chk_pass);
$display("No of basic burst read success:%0d",burst_read_pass);
$display("No of basic burst read failures:%0d",burst_read_fail);
$display("No of basic burst write success:%0d",burst_write_pass);
$display("No of basic burst write failures:%0d",burst_write_fail);
end

endmodule