FROM ubuntu:20.04

ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=Etc/UTC

RUN apt-get update && apt-get install -y \
  openjdk-11-jdk \
  python3 \
  python3-pip \
  git \
  curl \
  unzip \
  sudo \
  && rm -rf /var/lib/apt/lists/*

RUN pip install pwntools

RUN curl -L "https://github.com/joernio/joern/releases/latest/download/joern-install.sh" | sh

COPY execute_batch.py /scripts/execute_batch.py
COPY find.sc /scripts/find.sc

ENV TERM=xterm

CMD [ "python3",  "/scripts/execute_batch.py", "/targets" ]
