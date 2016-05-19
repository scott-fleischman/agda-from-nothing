agda = agda

solutions :
	$(agda) -i Solutions Solutions/Everything.agda

ideas :
	$(agda) -i Ideas/src Ideas/src/Everything.agda
