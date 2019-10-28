### Building the package
The code is written in `go` (version go1.10.4 linux/amd64). To build the package

```
cd wt
go build
```

To print the available operations within the tool, run

```
wt help
```

The benchmarks were run on a 64 bit machine running ubuntu using the WSL. To run the benchmarks locally

```
wt runtests
```
