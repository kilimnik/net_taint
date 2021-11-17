#!/usr/bin/env bash

dot -Tsvg methodGraph.dot -o methodGraph.svg
dot -Tsvg taintGraph.dot -o taintGraph.svg
