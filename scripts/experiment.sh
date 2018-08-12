
RULES=`ls rules`
cli='./bin/run.sh'

for rule in $RULES; do
  $cli example/tosca-conf.yml rules/$rule > /dev/null
  for file in `ls output`; do
    mv output/$file experiments/$rule.$file
  done
  echo "$rule [done]"
done

echo "FINISH"