
## Building a Docker Container
Run one of these commands based on your system
```
docker build . --platform linux/amd64 -t qualified-types-with-boolean-algebras
docker build . --platform linux/arm64 -t qualified-types-with-boolean-algebras
```

## Building Docker Image Files
Run the following commands to get an amd64 and arm64
```
docker build . --platform linux/amd64 -t qualified-types-with-boolean-algebras
docker image save -o "qualified-types-with-boolean-algebras-amd64.tar" qualified-types-with-boolean-algebras
docker build . --platform linux/arm64 -t qualified-types-with-boolean-algebras
docker image save -o "qualified-types-with-boolean-algebras-arm64.tar" qualified-types-with-boolean-algebras
```
Note that the second build commands overrides the first, so do not rearrange the
order here.

## Running and Loading the Docker Image Files
This should be explained in the artifact readme, but for ease of looking:

load a docker image (choose the appropriate name based on the system)
```
docker load --input qualified-types-with-boolean-algebras-amd64.tar
docker load --input qualified-types-with-boolean-algebras-arm64.tar
```

Run a docker image
```
docker run -it qualified-types-with-boolean-algebras
```
Both image files have the same tag, so when loaded, they behave identically.
