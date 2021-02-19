#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct history{
	
	int size;
	char *type;
	char *acc;
	
} Hist;

typedef struct node{
	
	int id;
	Hist *hist;
	struct node **sons;
	
} Node;

typedef struct nodelist{
	
	int size;
	Node **list;
	
} NodeList;

int main(){
	int trans_id, node_id;
	char type, acc;
	bool flag;
	int actual, i;
	NodeList *nodeList = malloc(sizeof(NodeList));
	nodeList->size = 0;
	
	//while not end of input
	while(scanf("%d %d %c %c", &trans_id, &node_id, &type, &acc) != EOF){
		flag = false;
		//check if the node already exist
		for(i = 0; i < nodeList->size; i++){
			if(nodeList->list[i]->id == node_id){
				flag = true;
				actual = i;
				break;
			}
		}
		//if the node doesn't exist create new
		if(!flag){
			Node *aux = malloc(sizeof(Node));
			aux->id = node_id;
			aux->sons = NULL;
			aux->hist = malloc(sizeof(Hist));
			aux->hist->size = 1;
			aux->hist->type = malloc(sizeof(char));
			aux->hist->type[0] = type;
			aux->hist->acc = malloc(sizeof(char));
			aux->hist->acc[0] = acc;
		}
		else{
			Hist *auxHist = nodeList->list[actual]->hist;
			auxHist->size += 1;
			auxHist->type = realloc(auxHist->type, sizeof(char)*auxHist->size);
			auxHist->type[auxHist->size-1] = type;
			auxHist->acc = realloc(auxHist->acc, sizeof(char)*auxHist->size);
			auxHist->acc[auxHist->size-1] = acc;
			
		}
		
	}
	
	return 0;
}

