Run one of these commands based on your system
```
docker build . --platform linux/amd64 -t qualified-types-with-boolean-algebras
docker build . --platform linux/arm64 -t qualified-types-with-boolean-algebras
```



# Stock build instructions

## Getting started
- Have docker installed and running.
  - Easiest method is to install [Docker Desktop](https://docs.docker.com/desktop/).
  - To check docker is running, you can run `docker --version` in your terminal.

#### Building the image
To build the docker image, run the following command in the folder with the Dockerfile:
```bash
$ docker build . -t qualified-types-with-boolean-algebras
```
This will build the image for your current architecture and tag it as
`qualified-types-with-boolean-algebras`. If you want to build it for a different
architecture, use the `--platform` option:
```bash
$ docker build . --platform linux/amd64 -t qualified-types-with-boolean-algebras
```
For our purposes the relevent values for `--platform` are:
- `linux/amd64`, meaning the container is a linux distribution (we use ubuntu) for x86\_64.
- `linux/arm64`, meaning the container is a linux distribution for aarch64.

#### Save image
To save an image to a file, use the following command:
```bash
$ docker image save -o "qualified-types-with-boolean-algebras-image.tar" qualified-types-with-boolean-algebras
```
Here the argument after the `-o` is the name of outputted file,
and `qualified-types-with-boolean-algebras` is the tag of the image you want to save.
The tag of the image will also be that is used when the image is loaded into
docker, so when creating files for multiple platforms, I suggest just
building them and saving them one at a time, since a build would overwrite
the previous image with the same tag.
This is just to ensure, whichever architecture is used by a reviewer,
the image tag would be the same.

1. Build for x86\_64: `docker build . --platform linux/amd64 -t qualified-types-with-boolean-algebras`
2. Save x86\_64 image: `docker image save -o "qualified-types-with-boolean-algebras-image-x86.tar" qualified-types-with-boolean-algebras`
3. Build for aarch64: `docker build . --platform linux/arm64 -t qualified-types-with-boolean-algebras`
4. Save aarch64 image: `docker image save -o "qualified-types-with-boolean-algebras-image-aarch64.tar" qualified-types-with-boolean-algebras`

#### Load image
Load the image into docker:
```bash
$ docker load --input qualified-types-with-boolean-algebras-image.tar
```
To check if this has been loaded correctly
you can run
```bash
$ docker images
```
If the `qualified-types-with-boolean-algebras` image is present in the list,
the load was successful.

### VS Code
- Have VS Code installed.
- Have the Dev Containers extension installed in VS Code.

The dev containers extension allows you to "hook into" a docker container
and operate it through VS Code.
#### devcontainer.json
The `devcontainer.json` file describes how VS Code should
operate with the docker container.
For our purposes I have made the following:
```json
{
    "image": "qualified-types-with-boolean-algebras",

    "workspaceFolder": "/workspace",

    "customizations": {
        "vscode": {
            "extensions": ["/flix.flix-1.40.0.vsix"]
        }
    }
}
```
The `image` entry, refers to the name of the docker container
explained above. Here we will assume docker is running and we have loaded the `qualified-types-with-boolean-algebras` image, so it can be used by VS Code.

The `workspaceFolder` specifies the workspace that should be opened by VS Code. If this is not provided, the folder the container is opened from, will be mounted in the docker container.
So to keep operation isolated to the container we will stick a workspace inside the container.
Since we use the `flix.jar` in the root of our VS Code workspace as a language server, the folder here is one with the `flix.jar` used to build the image.

The last part is the extensions we want to be used by
VS Code in the container. Since do not want to rely on networking, this refers to a flix extension file in the container, that will be added to the devcontainer by VS Code.

#### Running the devcontainer
With docker running.
If you open a folder with a `.devcontainer` folder
containing the `devcontainer.json` file inside in VS Code,
can you run the `Dev Containers: Reopen in Container` command in VS Code.
This should open the workspace inside the specified container with the extensions.
