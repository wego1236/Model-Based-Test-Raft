package main

import (
	"flag"
	"fmt"
)

var trace_file = flag.String("s", "stdin", "need string type")
var o = flag.String("o", "stdin", "need string type")

func main() {
	flag.Parse()

	fmt.Println("-s:", *trace_file)
	var controller Controller
	controller.init()
	controller.Trace_reader(*trace_file)

	fmt.Println("-o:", *o)
}
