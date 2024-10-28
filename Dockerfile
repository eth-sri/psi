FROM ubuntu

COPY . /opt/psi

RUN apt -qq update && apt -qq install -y wget unzip git xz-utils libxml2 gcc
RUN cd /opt/psi && ./dependencies-release.sh && ./build-release.sh && mkdir bin && mv psi ./bin

ENV PATH=$PATH:/opt/psi/bin
