FROM ubuntu@sha256:b59d21599a2b151e23eea5f6602f4af4d7d31c4e236d22bf0b62b86d2e386b8f

# Change the name of the workspace here.
ENV WORKSPACE=/workspace
ENV FLIX_JAR=$WORKSPACE/flix.jar

# Set work directory to /workspace.
WORKDIR $WORKSPACE

# Copy the contents of content/ into the container.
COPY content/ $WORKSPACE/

# Populate repository and install java 21 runtime.
RUN apt-get update &&\
    apt-get upgrade -y

RUN apt-get install curl -y &&\
    apt-get install unzip -y &&\
    apt-get install zip -y &&\
    apt-get install curl source &&\


# Add flix as an alias for easily calling the compiler.
RUN echo "alias flix='java -jar /workspace/flix.jar'" >> /root/.bashrc

# Make sure the shell is bash, to the alias is available.
SHELL ["/bin/bash", "-c"]
