for i in *.ml*
do
    newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
    if [ $i != $newi ]
    then
        echo "Moving " $i "to" $newi;
        mv $i tmp;
        mv tmp $newi;
    fi
done
