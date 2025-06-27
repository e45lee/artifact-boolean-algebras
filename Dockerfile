FROM rocq/rocq-prover:9.0-native

# Change the name of the workspace here.
ENV WORKSPACE=/workspace
ENV FLIX_JAR=$WORKSPACE/flix-compiler/flix.jar

# Set work directory to /workspace.
WORKDIR $WORKSPACE

RUN sudo apt-get update
RUN sudo apt-get upgrade -y
RUN sudo apt-get install wget lsb-release -y
RUN wget https://packages.microsoft.com/config/debian/$(lsb_release -rs)/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
RUN sudo dpkg -i packages-microsoft-prod.deb
RUN sudo apt-get install curl -y
RUN sudo apt-get install unzip -y
RUN sudo apt-get install zip -y
    # sudo curl -s "https://get.sdkman.io" | bash

# RUN sudo /bin/bash -c "source /home/.sdkman/bin/sdkman-init.sh && sdk install java 21.0.2-open && cd flix-compiler/flix-source && ./gradlew build"


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
