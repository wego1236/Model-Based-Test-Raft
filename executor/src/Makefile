SHELL := /bin/bash

.PHONY: build clean

build :
	go build config.go controller.go main.go trace.go

clean:
	rm -rf config controller trace