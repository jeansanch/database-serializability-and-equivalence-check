// Alejandro Gemin Rosales - GRR20160188
// Jean Carlo Sanchuki Filho - GRR20185527
// Database Serializability and Equivalence Verification

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

//transaction history
typedef struct history{ 
	
	int size;
	char *type;
	char *acc;
	int *id;
	
} Hist;

typedef struct node{
	
	int id;
	Hist *hist;
	int size;//sons size
	struct node **con;
	
} Node;

typedef struct nodeList{
	
	Node *self;
	struct nodeList *next;
	
} NodeList;

typedef struct stackId{

	int id;
	struct stackId *next;

} StackId;

bool isSerial(NodeList *list);
int isSerialAux(Node **list, int size, Node *start);
void printResult(NodeList *list, bool ser, bool ev);
char toUpper(char type);

int printCounter;
int stackSize = 0;

int main(){
	int trans_id, node_id;
	char type, acc;
	bool flag, skip, serial, eVision = true, flagConnected, in;
	int i, j, k, l, m;
	StackId *stackId = NULL;
	Hist *auxHist, *auxHist2;
	NodeList *nodeList = NULL;
	NodeList *aux, *current, *newNode;
	bool init = true;
	StackId *auxNL;
	//while not end of input
	while(scanf("%d %d %c %c", &trans_id, &node_id, &type, &acc) != EOF){
		skip = false;
		type = toUpper(type);
		if(!init){
			if(stackId == NULL){
				serial = isSerial(nodeList);
				if(!serial)
					eVision = false;
				printResult(nodeList, serial, eVision);
				//Initialize as true, but will be verified later
				eVision = true;
				//Clear memory
					aux = nodeList;
				while(aux != NULL){
					aux = nodeList->next;
					free(nodeList->self->con);
					free(nodeList->self->hist);
					free(nodeList->self);
					nodeList = aux;
				}
			}
		}
		else{
			init = false;
		}
		current = NULL;
		aux = nodeList;
		flag = false;
		//Check if the node already exist
		if(aux != NULL){
			if(aux->next == NULL){
				if(aux->self->id == node_id){
					flag = true;
					current = aux;
				}
				skip = true;
			}
		}
		else{
			skip = true;
		}
	
		if(!skip){
			if(aux->self->id == node_id){
				flag = true;
				current = aux;
			}
			else{
				do{
					aux = aux->next;
					if(aux->self->id == node_id){
						flag = true;
						current = aux;
						break;
					}
				}while(aux->next != NULL);
			}
		}
		//if the node doesn't exist create new
		if(!flag){
			if(stackId == NULL){
				stackId = malloc(sizeof(stackId));
				stackId->id = node_id;
				stackId->next = NULL;
				stackSize++;
			}
			else{
				StackId *auxStack;
				StackId *auxStack2;
				auxStack = malloc(sizeof(StackId));
				auxStack->id = node_id;
				auxStack->next = NULL;
				auxStack2 = stackId;
				while(auxStack2->next != NULL){
					auxStack2 = auxStack2->next;
				}
				auxStack2->next = auxStack;
				stackSize++;
				
			}
			Node *auxn = malloc(sizeof(Node));
			auxn->id = node_id;
			auxn->size = 0;
			auxn->con = NULL;
			auxn->hist = malloc(sizeof(Hist));
			auxn->hist->size = 1;
			auxn->hist->type = malloc(sizeof(char));
			auxn->hist->type[0] = type;
			auxn->hist->acc = malloc(sizeof(char));
			auxn->hist->acc[0] = acc;
			auxn->hist->id = malloc(sizeof(int));
			auxn->hist->id[0] = trans_id;
			
			newNode = malloc(sizeof(NodeList));
			newNode->self = auxn;
			newNode->next = NULL;
			if(nodeList == NULL){
				nodeList = newNode;
				current = nodeList;
			}
			else{
				aux->next = newNode;
				current = aux->next;
			} 
		}
		else{
			auxHist = current->self->hist;
			auxHist->size += 1;
			auxHist->type = realloc(auxHist->type, sizeof(char)*auxHist->size);
			auxHist->type[auxHist->size-1] = type;
			auxHist->acc = realloc(auxHist->acc, sizeof(char)*auxHist->size);
			auxHist->acc[auxHist->size-1] = acc;
			auxHist->id = realloc(auxHist->id, sizeof(int)*auxHist->size);
			auxHist->id[auxHist->size-1] = trans_id;
		}
		
		switch(type){
			case 'R':
			// creating nodes connections if conditions met
				aux = nodeList;
				while(aux != NULL){
					if(aux->self->id != node_id){
						auxHist = aux->self->hist;
						flagConnected = false;
						for(i = 0; i < auxHist->size; i++){
							if(auxHist->type[i] == 'W' && auxHist->acc[i] == acc){
								for(j = 0; j < current->self->size; j++){
									if(current->self->con[j] == aux->self)
										flagConnected = true;
								}
								if(!flagConnected){
									current->self->size += 1;
									current->self->con = realloc(current->self->con, sizeof(Node)*current->self->size);
									current->self->con[current->self->size-1] = aux->self;
								}
							}
						}
					}
					aux = aux->next;
				}
				// Checking if EV is not possible
				// Step 1: Check if there is another write on the same account by another node
				// Step 2: Check if the node that made the write on step 1 has a read before
				// Step 3: Check if the account on the step 2 read, has a third node that has a write on that account
				// Step 4: Check if first Node has another read that has a write on the third Node
				// Step 5: Check if transactions order is Nodes 3,1,2,1
				// If everything meet, it is impossible to have equivalent vision, because Node 1 will always conflict with someone
				// Verification for the conflict of different writings
				if(eVision){
					aux = nodeList;
					NodeList *aux2 = nodeList;
					// Start of Step 1:
					while(aux != NULL){
						if(aux->self->id != node_id){
							auxHist = aux->self->hist;
							for(i = 0; i < auxHist->size; i++){
								if(auxHist->type[i] == 'W' && auxHist->acc[i] == acc){
									// Start of Step 2:
									for(j = i-1; j >= 0; j--){
										if(auxHist->type[j] == 'R'){
											// Start of Step 3:
											aux2 = nodeList;
											while(aux2 != NULL){
												if(aux2->self->id != node_id && aux2->self->id != aux->self->id){
													auxHist2 = aux2->self->hist;
													for(k = 0; k < auxHist2->size; k++){
														if(auxHist2->type[k] == 'W' && auxHist2->acc[k] == auxHist->acc[j]){
															// Start of Step 4:
															for(l = 0; l < auxHist2->size; l++){
																for(m = 0; m < current->self->hist->size; m++){
																	if(auxHist2->type[l] == 'W' && current->self->hist->type[m] == 'R' && auxHist2->acc[l] == current->self->hist->acc[m]){
																		// Start of Step 5:
																		if(auxHist2->id[l] < current->self->hist->id[m] && current->self->hist->id[m] < auxHist->id[j] && auxHist->id[j] < trans_id)
																			eVision = false;
																	}
																}
															}
														}
													}
												}
												aux2 = aux2->next;
											}
										}
									}
								}
							}
						}
						aux = aux->next;
					}
				}
			break;

			case 'W':
			// creating nodes connections if necessary;
				aux = nodeList;
				flagConnected = false;
				while(aux != NULL){
					if(aux->self->id != node_id){
						auxHist = aux->self->hist;
						flagConnected = false;
						for(i = 0; i < auxHist->size; i++){
							if((auxHist->type[i] == 'R' || auxHist->type[i] == 'W') && auxHist->acc[i] == acc){
								for(j = 0; j < current->self->size; j++){
									if(current->self->con[j] == aux->self)
										flagConnected = true;
								}
								if(!flagConnected){
									current->self->size += 1;
									current->self->con = realloc(current->self->con, sizeof(Node)*current->self->size);
									current->self->con[current->self->size-1] = aux->self;
								}
							}
						}
					}
					aux = aux->next;
				}
			break;

			case 'C':
				in = false;
				auxNL = stackId;
				// If there is only one item in the list
				if(auxNL != NULL){
					if(auxNL->id == node_id){
						if(auxNL->next == NULL){
							stackId = NULL;
						}
						else{
						*auxNL = *auxNL->next;
						}
						in = true;
					}
				}
				if(!in){
					while(auxNL != NULL){
						if(auxNL->next != NULL){
							if(auxNL->next->id == node_id){
								if(auxNL->next->next == NULL){
									auxNL->next = NULL;
								}
								else{
									*auxNL->next = *auxNL->next->next;
								}
								break;
							}
						}
						auxNL = auxNL->next;
					}
				}
				stackSize--;
			break;
		}
	}
	serial = isSerial(nodeList);
	if(!serial)
		eVision = false;
	printResult(nodeList, serial, eVision);
	eVision = true;
	// Clear memory
	while(aux != NULL){
		aux = nodeList->next;
		free(nodeList->self->con);
		free(nodeList->self->hist);
		free(nodeList->self);
		nodeList = aux;
	}
	return 0;
}

char toUpper(char type){
	if(type < 123 && type > 96){
		type = type - 32; 
	}
	return type;
}

//bool isSerial(NodeList *list){
//	NodeList *aux, *auxR;
//	aux = list;
//	int i, j;
//	while(aux != NULL){
//		if(aux->self->con != NULL){
//			for(i = 0; i < aux->self->size; i++){
//				for(j = 0; j < aux->self->con[i]->size; j++){
//					if(aux->self->con[i]->con[j] == aux->self)
//						return false;
//				}
//			}
//		}
//		aux = aux->next;
//	}
//	return true;
//} 

bool isSerial(NodeList *list){
	NodeList *aux;
	aux = list;
	int total = 0;
	while(aux != NULL && total == 0){
		if(aux->self->con != NULL){
			total = isSerialAux(aux->self->con, aux->self->size, aux->self);
		}
		aux = aux->next;
	}
	return total > 0 ? true : false;
}

int isSerialAux(Node **list, int size, Node *start){
	int i, total = 0;
	for(i = 0; i < size; i++){
		if(list[i] == start)
				return 1;
		if(list[i]->con != NULL){	
			total = isSerialAux(list[i]->con, list[i]->size, start);
		}
	}
	return total;
}

void printResult(NodeList *list, bool ser, bool ev){
	NodeList *aux = list;
	printCounter++;
	printf("%d ", printCounter);
	while(aux != NULL){
		printf("%d", aux->self->id);
		if(aux->next != NULL){
			printf(",");
		}
		aux = aux->next;
	}
	if(ser){
		printf(" SS ");
	}
	else{
		printf(" NS ");
	}
	if(ev){
		printf("SV\n");
	}
	else{
		printf("NV\n");
	}
}
