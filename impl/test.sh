set -o pipefail && make && cat examples/suite.txt | xargs -I {} ./main.sh examples/{}
