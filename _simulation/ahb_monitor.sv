module ahb_monitor(ahb_lite_bus bus);



int basic_transfer_pass;
int basic_transfer_fail;
int hready_chk_pass;
int hready_chk_fail;
int busy_transfer_fail;
int busy_transfer_pass;

property basic_transfer;
@(posedge bus.HCLK)disable iff(!bus.HRESETn)
(!bus.Master.HWRITE && bus.Master.HREADY)|->##1 !($isunknown(bus.Master.HRDATA));
   endproperty

assert property (basic_transfer)
basic_transfer_pass++;
else 
begin
basic_transfer_fail++;
end


property HREADY_check;
@(posedge Bus.HCLK) (bus.Master.HREADY == 1'b0) |=> $stable (bus.Master.HADDR && bus.Master.HWRITE && bus.Master.HWDATA) ;
endproperty

assert property (HREADY_check)
hready_chk_pass++;
else 
hready_chk_fail++;

property busy_transfer;
@(posedge bus.HCLK)disable iff(!bus.HRESETn)
((bus.Master.HTRANS==2'b01)&&bus.Master.HREADY)|-> $stable(bus.Master.HADDR);
endproperty

assert property (busy_transfer)
busy_transfer_pass++;
else
busy_transfer_fail++;

initial
begin
$display("No of basic transfer failures:%0d",basic_transfer_pass);
$display("No of basic transfer success:%0d",basic_transfer_pass);
$display("No of hready_check failures:%0d",hready_chk_fail);
$display("No of hready_check success:%0d",hready_chk_pass);
$display("No of busy transfer failures:%0d",busy_transfer_fail);
$display("No of busy transfer success:%0d",busy_transfer_pass);
end

endmodule