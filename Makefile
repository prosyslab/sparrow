SPARROW=sparrow
VIS=sparrow-vis

all:
	-dune fmt
	dune build src/main.exe
	dune build src/vis.exe
	@ln -sf ../_build/default/src/main.exe bin/$(SPARROW)
	@ln -sf ../_build/default/src/vis.exe bin/$(VIS)

test: all
	dune build test/test.exe
	dune test
	@script/check-format
	@cd test; ../_build/default/test/test.exe

promote:
	dune promote
	@script/promote

clean:
	dune clean
	@rm -rf bin/$(SPARROW)
	@rm -rf bin/$(VIS)
