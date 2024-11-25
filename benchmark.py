import subprocess
import time
import os
import tempfile
import json

graphs = [
    ("cnr-2000", 1),
    ("in-2004", 1),
    ("eu-2005", 1),
    ("uk-2005", 1),
    ("it-2004", 1),
    ("arabic-2005", 1),
]

base_datasets = "data.law.di.unimi.it/webdata/"

rust_path = "./target/release/webgraph-algo"
if os.name == "nt":
    rust_path = rust_path + ".exe"
classpath_sep = ";" if os.name == "nt" else ":"
java_base_command = f'java -cp "./java/webgraph.jar{classpath_sep}./java/lib/*"'

build_executable_command = "cargo build --release --bin webgraph-algo"
install_webgraph_command = "cargo install --git https://github.com/vigna/webgraph-rs.git webgraph"

def timer(command: str) -> float:
    print(command)
    start = time.time()
    subprocess.run(command, shell=os.name != "nt")
    end = time.time()
    return end - start

def log_and_run(command: str):
    print(command)
    subprocess.run(command, shell=True)

def prepare_graph(graph_name: str, path: str) -> str:
    basename = f"{path}{os.sep}{graph_name}"
    print(f"Downloading base graph {graph_name}...")
    log_and_run(f'curl -o "{basename}.graph" {base_datasets}{graph_name}/{graph_name}.graph')
    log_and_run(f'curl -o "{basename}.properties" {base_datasets}{graph_name}/{graph_name}.properties')
    print(f"Downloading transposed graph {graph_name}...")
    log_and_run(f'curl -o "{basename}-t.graph" {base_datasets}{graph_name}/{graph_name}-t.graph')
    log_and_run(f'curl -o "{basename}-t.properties" {base_datasets}{graph_name}/{graph_name}-t.properties')
    print(f"Padding downloaded graphs...")
    log_and_run(f"webgraph run pad {basename} u32")
    log_and_run(f"webgraph run pad {basename}-t u32")
    print(f"Computing offsets...")
    log_and_run(f"webgraph build offsets {basename}")
    log_and_run(f"webgraph build offsets {basename}-t")
    print(f"Computing elias fano...")
    log_and_run(f"webgraph build ef {basename}")
    log_and_run(f"webgraph build ef {basename}-t")
    print(f"Computing cumulative outdegree...")
    log_and_run(f"webgraph build dcf {basename}")

    return basename

results = {}

log_and_run(build_executable_command)
log_and_run(install_webgraph_command)

for (graph, runs) in graphs:
    with tempfile.TemporaryDirectory() as tmpdir:
        graph_basename = prepare_graph(graph, tmpdir)

        results[graph] = {}
        results[graph]["tarjan"] = {}
        results[graph]["tarjan"]["java"] = []
        results[graph]["tarjan"]["rust"] = []
        results[graph]["diameter"] = {}
        results[graph]["diameter"]["java"] = []
        results[graph]["diameter"]["rust"] = []
        results[graph]["hyperball"] = {}
        results[graph]["hyperball"]["java"] = []
        results[graph]["hyperball"]["rust"] = []

        # Tarjan
        java_command = f"{java_base_command} it.unimi.dsi.webgraph.algo.StronglyConnectedComponents {graph_basename}"
        rust_command = f"{rust_path} tarjan {graph_basename}"

        for _ in range(runs):
            results[graph]["tarjan"]["java"].append(timer(java_command))
        for _ in range(runs):
            results[graph]["tarjan"]["rust"].append(timer(rust_command))

        # Diameter
        java_command = f"{java_base_command} it.unimi.dsi.webgraph.algo.SumSweepDirectedDiameterRadius {graph_basename} -m -l RADIUS_DIAMETER"
        rust_command = f"{rust_path} diameter {graph_basename}"

        for _ in range(runs):
            results[graph]["diameter"]["java"].append(timer(java_command))
        for _ in range(runs):
            results[graph]["diameter"]["rust"].append(timer(rust_command))

        # Hyperball
        log2m = 6
        
        java_command = f"{java_base_command} it.unimi.dsi.webgraph.algo.HyperBall {graph_basename} {graph_basename}-t -o -l {log2m}"
        rust_command = f"{rust_path} hyperball {graph_basename} {log2m}"

        for _ in range(runs):
            results[graph]["hyperball"]["java"].append(timer(java_command))
        for _ in range(runs):
            results[graph]["hyperball"]["rust"].append(timer(rust_command))

print(results)
