package main

import (
	"flag"
	"fmt"
	"log"
	"os"
)

var trace_file = flag.String("s", "stdin", "need string type")
var o = flag.String("o", "stdin", "need string type")

// Debugging
//const Debug = false

const Debug = true

func DPrintf(format string, a ...interface{}) (n int, err error) {
	if Debug {
		log.Printf(format, a...)
	}
	return
}

func main() {
	flag.Parse()

	fmt.Println("-s:", *trace_file)
	var controller Controller
	controller.init()
	if *trace_file == "stdin" {
		controller.Trace_reader(os.Stdin)
	} else {
		fi, err := os.Open(*trace_file)
		if err != nil {
			fmt.Printf("Error: %s\n", err)
			return
		}
		controller.Trace_reader(fi)
	}
	controller.Trace_executor()
	fmt.Println("-o:", *o)
}
