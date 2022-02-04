import os
import shutil

PROJECT_PATHS = "/home/daniel/theZoo"
OUT_FOLDER = "out"

projects = os.listdir(PROJECT_PATHS)
projects = list(filter(lambda x: os.path.isdir(f"{PROJECT_PATHS}/{x}"), projects))

for project in projects:
    project_path = f"{PROJECT_PATHS}/{project}"

    if os.path.isdir(f"{project_path}/{OUT_FOLDER}") and len(os.listdir(f"{project_path}/{OUT_FOLDER}")) == 0:
        print(f"Deleting {project}")

        shutil.rmtree(project_path)
