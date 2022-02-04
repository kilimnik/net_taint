#!/usr/bin/python3

from pwn import *
import os
import time
import multiprocessing
import glob
import sys
import shutil

# context.log_level = 'debug'

JOERN_PATH = "/usr/local/bin/joern"
SCRIPT_PATH = "/scripts/execute_batch.py"

PROJECT_PATHS = ""

MARKER = b"REMOVED_TEMP"

def replace_files(path, find, replace, ending=b""):
    for filepath in glob.iglob(f'{path}/**/*{ending}', recursive=True):
        with open(filepath, "rb") as file:
            s = file.read()
        s = s.replace(find, replace)
        with open(filepath, "wb") as file:
            file.write(s)

def remove_pre(path):
    replace_files(path, b"#if", b"//" + MARKER + b"#if", ending=".c*")
    replace_files(path, b"#endif", b"//" + MARKER + b"#if", ending=".c*")
    replace_files(path, b"#elif", b"//" + MARKER + b"#if", ending=".c*")

def unremove_pre(path):
    replace_files(path, b"//" + MARKER + b" ", b"", ending=".c*")


def run(p, script_path, project_path):
    project = os.path.basename(project_path)
    start_time = time.perf_counter()

    remove_pre(project_path)
    print(f"Loading {project}")
    p.send(f"importCode.c(inputPath=\"{project_path}\")\n".encode())
    unremove_pre(project_path)

    out = p.recvuntil(b"joern>")

    print(f"Tainting {project}")
    p.send(f"runScript(\"{script_path}\", Map(), cpg)\n".encode())
    out += p.recvuntil(b"joern>")
    out += p.recvuntil(b"joern>")

    time_ran = time.perf_counter() - start_time
    print(f"Finished {project} in {time_ran:0.4f} seconds\n")

    row = f"{project},{time_ran}\n"
    while True:
        try:
            with open(f"{PROJECT_PATHS}/out/out.csv", "a") as f:
                f.write(row)
            break
        except ValueError:
            pass

    while True:
        try:
            with open(f"{PROJECT_PATHS}/out/{project}.out", "wb") as f:
                f.write(out)
            break
        except ValueError:
            pass

def get_process():
    p = process(f"{JOERN_PATH} --nocolors", shell=True)
    p.recvuntil(b"joern>")

    return p

def chunker_list(seq, size):
    return (seq[i::size] for i in range(size))


def main():
    global PROJECT_PATHS

    def worker(i, projects):
        print(f"Process {i} starting.")

        p = get_process()

        for i, project in enumerate(projects):
            print(f"Project {project} {i+1} out of {len(projects)}")
            project_path = f"{PROJECT_PATHS}/{project}"

            run(p, SCRIPT_PATH, project_path)

        p.kill()

        print(f"Process {i} finished.")

    if len(sys.argv) != 2:
        print("Usage: python3 execute_batch.py <Directory of programs>")
        return

    PROJECT_PATHS = sys.argv[1]

    if (os.path.exists(f"{PROJECT_PATHS}/out")):
        shutil.rmtree(f"{PROJECT_PATHS}/out")
    os.mkdir(f"{PROJECT_PATHS}/out")

    projects = os.listdir(PROJECT_PATHS)
    projects = list(filter(lambda x: os.path.isdir(f"{PROJECT_PATHS}/{x}") and x != "out", projects))
    projects.sort()

    print(f"Found {len(projects)} projects\n")

    worker_count = multiprocessing.cpu_count() - 1
    worker_count = min(worker_count, len(projects))
    print(f"{worker_count} processes")

    projects_chunks = list(chunker_list(projects, worker_count))

    workers = []
    for i, projects in enumerate(projects_chunks):
        d = multiprocessing.Process(target=worker, args=[i, projects])
        d.daemon = True

        d.start()

        workers.append(d)

    for worker in workers:
        worker.join()

if __name__ == "__main__":
    main()
