SPARROW=sparrow
VIS=sparrow-vis

all:
	dune build src/main.exe
	dune build src/vis.exe
	@cd bin; ln -sf ../_build/default/src/main.exe $(SPARROW); ln -sf ../_build/default/src/vis.exe $(VIS)

test: all
	dune build test/test.exe
	@cd test; ../_build/default/test/test.exe

promote:
	@script/promote

clean:
	dune clean
