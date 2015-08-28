PYRET = node ~/git/pyret-lang/build/phase1/main-wrapper.js

all: compile test portTest

compile:
	$(PYRET) --compile-module-js util.arr > util.arr.js
	$(PYRET) --compile-module-js atom.arr > atom.arr.js
	$(PYRET) --compile-module-js term.arr > term.arr.js
	$(PYRET) --compile-module-js sugar.arr > sugar.arr.js

portTest:
	$(PYRET) port-test.arr

test:
	$(PYRET) tests.arr
