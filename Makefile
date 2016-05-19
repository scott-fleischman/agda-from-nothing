agda = agda

default : type-check

everything :
	@echo "module Everything where" > Solutions/Everything.agda
	@find Solutions -name '*.agda' -not -path 'Solutions/Everything.agda' | sed -e 's/Solutions\///;s/\//./g;s/\.agda$$//;s/^/import /' >> Solutions/Everything.agda

type-check : everything
	$(agda) -i Solutions Solutions/Everything.agda
