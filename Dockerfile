FROM rocq/rocq-prover:9.0-native

# Change the name of the workspace here.
ENV WORKSPACE=/workspace
ENV FLIX_JAR=$WORKSPACE/flix-compiler/flix.jar

# Set work directory to /workspace.
WORKDIR $WORKSPACE

# Populate repository and install java 21 runtime.
RUN sudo apt-get update &&\
    sudo apt-get upgrade -y &&\
    sudo apt-get install wget lsb-release -y &&\
    wget https://packages.microsoft.com/config/debian/$(lsb_release -rs)/packages-microsoft-prod.deb -O packages-microsoft-prod.deb &&\
    sudo dpkg -i packages-microsoft-prod.deb &&\
    sudo apt-get update &&\
    sudo apt-get install curl -y &&\
    sudo apt-get install unzip -y &&\
    sudo apt-get install zip -y &&\
    curl -s "https://get.sdkman.io" | bash

RUN /bin/bash -c "source /root/.sdkman/bin/sdkman-init.sh && sdk install java 21.0.2-open && cd flix-source && ./gradlew build"


# Copy the contents of content/ into the container.
ADD --chown=1000:1000 flix-compiler/content/ $WORKSPACE/flix-compiler/
ADD --chown=1000:1000 proofs/ $WORKSPACE/proofs/

# Add flix as an alias for easily calling the compiler.
RUN echo "alias flix='java -jar /workspace/flix.jar'" >> /home/rocq/.bashrc

# Build the proofs
RUN cd $WORKSPACE/proofs && make
RUN cd $WORKSPACE/proofs && make coqdoc

# Make sure the shell is bash, to the alias is available.
SHELL ["/bin/bash", "-c"]
