module Plugin

import orig::Parser;

import util::IDE;

void main(){
	str lang = "AlleAlle";

	registerLanguage(lang,"alle", parseFile);
}