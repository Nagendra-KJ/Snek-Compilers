echo "All operations are done on the number 1, with innermost operation done first. eg add_sub means (add1 (sub1 1))";
echo "All outputs are written in the file outputs.txt";
> output.txt;

for f in test/*.snek; do
base=$(basename $f);
filename=${base%.*};
dir=$(dirname $f);
run=$(echo $dir/$filename.run);
asm=$(echo $dir/$filename.s);

echo
echo "The snek program $filename is:" | tee -a output.txt;

echo "🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍";
echo
cat $f | tee -a output.txt;
echo
echo "🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍🐍";

echo

echo "Making the program:";
echo

make $run;
make $asm;
echo

echo "The resulting assembly program is:" | tee -a output.txt;
echo "**************************************************************************";
cat $asm | tee -a output.txt;
echo "**************************************************************************";
echo
echo "The output for the snek program $filename is:" $(./$run) | tee -a output.txt;
done
