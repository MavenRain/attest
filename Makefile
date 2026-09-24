.PHONY: build check test gates

build:
	python3 -P dev/build.py

check:
	python3 -P dev/build.py --check

test: build
	python3 -P dev/test-all.py

gates:
	zsh -f dev/gates.sh
