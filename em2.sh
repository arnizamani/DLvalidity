#!/usr/bin/env bash
#SBATCH -A C3SE103-13-4
#SBATCH -p glenn
#SBATCH -N 1
#SBATCH -n 1
#SBATCH -c 16
#SBATCH -t 1:00:00
#SBATCH --mail-user abdulra@chalmers.se
#SBATCH --mail-type=end
# srun  -o proof-%j.log
#SBATCH -o proof-%j.log

echo "Starting at "
date

./DLvalidityBfs em2.txt em2box.txt 6 30 +RTS -N16 -RTS
wait
echo "Finished at "
date

# End script
