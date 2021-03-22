FROM dlanguage/dmd
LABEL "Version"="1.0"

COPY . /opt/psi

RUN apt -qq update && apt -qq install -y wget unzip
RUN cd /opt/psi && ./dependencies-release.sh && ./build-release.sh && mkdir bin && mv psi ./bin

RUN echo "export PATH=$PATH:/opt/psi/bin" >> /root/.bashrc

WORKDIR /root

ENTRYPOINT ["bash"]

