#Sameer Ghewari, Portland State University, Feb 2015
#This makefile is for TBX BFM Example - Simple booth

#Specify the mode- could be either puresim or veloce
#Always make sure that everything works fine in puresim before changing to veloce

make MODE = puresim

#make all does everything
all: work build run

#Create respective work libs and map them 
work:
	vlib work.$(MODE)
	vmap work work.$(MODE)
	
#Compile/synthesize the environment
build:
	vlog ahb_lite_defs.sv			#Compile the package
	 
ifeq ($(MODE),puresim)		#If mode is puresim, compile everything else
	vlog ahb_lite_bus.sv 					#Complie the
	vlog ahb_lite_tb_interface.sv			#Compile the interface
	vlog ahb_lite_mem_ctrl.sv				#Compile the memory DUT 
	vlog ahb_lite_slave_wrapper.sv 			#Compile 
	vlog dual_port_RAM.sv 					#compile the dual port RAM
	vlog ahb_lite_tb_sequencer.sv             #
	vlog ahb_lite_dut_top.sv				#Compile the HDL top 
	vlog ahb_lite_tb_top.sv					#Compile the testbench
	velhvl -sim $(MODE)
else
	velanalyze ahb_lite_defs.sv		#Analyze the package for synthesis 
	velanalyze ahb_lite_bus.sv 					#Complie the
	velanalyze ahb_lite_tb_interface.sv			#Compile the interface
	velanalyze ahb_lite_mem_ctrl.sv				#Compile the memory DUT 
	velanalyze ahb_lite_slave_wrapper.sv 			#Compile 
	velanalyze dual_port_RAM.sv 					#compile the dual port RAM
	velanalyze -hdl verilog -extract_hvl_info ahb_lite_tb_sequencer.sv        #
	velanalyze -hdl verilog -extract_hvl_info +define+QUESTA ahb_lite_tb_top.sv	#Analyze the HVL for external task calls in BFM 
	vlog -mfcu ahb_lite_tb_sequencer.sv ahb_lite_tb_top.sv						#else, synthesize!
	velanalyze ahb_lite_dut_top.sv				#Compile the HDL top 
#	velanalyze ahb_lite_tb_top.sv					#Compile the testbench
	
	
	velcomp -top ahb_lite_dut_top  	#Synthesize!
	velhvl -sim $(MODE) 
endif

run:
	vsim -c -novopt -do "run -all" ahb_lite_dut_top ahb_lite_tb_top TbxSvManager	#Run all 
	cp transcript transcript.$(MODE)		#Record transcript 

norun:	#No run lets you control stepping etc. 
	vsim -c +tbxrun+norun ahb_lite_tb_top ahb_lite_dut_top -cpppath $(CPP_PATH)
	cp transcript transcript.$(MODE)

clean:
	rm -rf tbxbindings.h modelsim.ini transcript.veloce transcript.puresim work work.puresim work.veloce transcript *~ vsim.wlf *.log dgs.dbg dmslogdir veloce.med veloce.wave veloce.map velrunopts.ini edsenv 
	


