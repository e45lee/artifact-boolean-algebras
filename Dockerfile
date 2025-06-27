FROM rocq/rocq-prover:9.0-native

# Change the name of the workspace here
ENV WORKSPACE=/workspace
ENV FLIX_JAR=$WORKSPACE/evaluation/flix.jar

# Set work directory to /workspace
WORKDIR $WORKSPACE

# Copy the container content
ADD --chown=1000:1000 evaluation/ $WORKSPACE/evaluation/
ADD --chown=1000:1000 proofs/ $WORKSPACE/proofs/
ADD --chown=1000:1000 README.md $WORKSPACE/README.md

# Install required software
RUN sudo apt-get update
RUN sudo apt-get upgrade -y
RUN sudo apt-get install wget lsb-release -y
RUN sudo apt install nano -y
RUN sudo apt install vim -y
RUN sudo apt-get install curl -y
RUN sudo apt-get install unzip -y
RUN sudo apt-get install zip -y
RUN sudo curl -s "https://get.sdkman.io" | bash

# Build the flix compiler once to download online dependencies
# These have to be sequenced for 'source' and 'JAVA_PATH' to persist
RUN source /home/rocq/.sdkman/bin/sdkman-init.sh &&\
    sdk install java 21.0.2-open &&\
    cd evaluation/flix-compiler-source &&\
    ./gradlew build

# Build the proofs
RUN cd $WORKSPACE/proofs && make
RUN cd $WORKSPACE/proofs && make coqdoc

# Add flix as an alias for easily calling the compiler and sure the shell is
# bash, so the alias is available
RUN echo "alias flix='java -jar /workspace/evaluation/flix.jar'" >> /home/rocq/.bashrc
SHELL ["/bin/bash", "-c"]
