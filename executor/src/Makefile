SHELL := /bin/bash

.PHONY: build clean check

CHECK_DIR ?=

build :
	go build config.go controller.go main.go trace.go

check: build
	if [ -d "$(CHECK_DIR)" ]; then \
		for i in "$(CHECK_DIR)"/*; do \
			echo "$${i}";\
			./config -s "$${i}"; \
		done; \
	else \
		echo Usage: make check CHECK_DIR=some_dir [MEMORY_CHECK=yes]; \
	fi

clean:
	rm -rf config controller trace