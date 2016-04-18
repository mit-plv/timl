set -o pipefail && make -C . && xargs -a examples/suite.txt -I {} ./main.sh examples/{}
