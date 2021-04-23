#include "skel.h"
#include <netinet/if_ether.h>
#include "queue.h"

//structura pentru elementele tabelei de rutare
typedef struct {
	struct in_addr prefix;
	struct in_addr next_hop;
	struct in_addr masca;
	int interfata;
} rtable;

//structura pentru elementele tabelei de arp
typedef struct {
	unsigned int ip;
	unsigned char mac[6]; 
} arpTable;

//structura pentru lista
typedef struct nod {
	arpTable info;
	struct nod *next;
} Nod, *List, **AList;

//functie de numarare e liniilor din fisierul cu tabela de rutare
int count() {
	FILE *file = fopen("rtable.txt", "r");
	char c;
	int count = 0;
	for (c = getc(file); c != EOF; c = getc(file)) 
        if (c == '\n') 
            count++; 
    fclose(file);
	return count;
}

//funtie de adaugare in lista
void addList(AList l, arpTable info) {
	List nou = malloc(sizeof(info) + sizeof(struct nod));
	nou->info = info;
	nou->next = NULL;
	List aux = (*l);
	nou->next = aux;
	(*l) = nou;
}

//funtie de sortare
void merge(rtable arr[], int l, int m, int r) 
{ 
    int i, j, k; 
    int n1 = m - l + 1; 
    int n2 =  r - m; 

    rtable L[n1], R[n2]; 
  
    for (i = 0; i < n1; i++) 
        L[i] = arr[l + i]; 
    for (j = 0; j < n2; j++) 
        R[j] = arr[m + 1+ j]; 
  
    i = 0; 
    j = 0; 
    k = l;
    while (i < n1 && j < n2) 
    { 
        if (L[i].prefix.s_addr < R[j].prefix.s_addr) 
        { 
            arr[k] = L[i]; 
            i++; 
        } 
        else
        { 
        	if(L[i].prefix.s_addr == R[j].prefix.s_addr) {
        		if(L[i].masca.s_addr < R[j].masca.s_addr) {
        			arr[k] = L[i]; 
            		i++; 
        		} else {
        			arr[k] = R[j]; 
            		j++;
        		}
        	} else {
            	arr[k] = R[j]; 
            	j++;
            } 
        } 
        k++; 
    } 
  
    while (i < n1) 
    { 
        arr[k] = L[i]; 
        i++; 
        k++; 
    } 
  
    while (j < n2) 
    { 
        arr[k] = R[j]; 
        j++; 
        k++; 
    } 
} 

//funtie de sortare
void mergeSort(rtable arr[], int l, int r) 
{ 
    if (l < r) 
    { 
        int m = l+(r-l)/2; 
        mergeSort(arr, l, m); 
        mergeSort(arr, m+1, r); 
  
        merge(arr, l, m, r); 
    } 
} 

//functie de cautare binara in tabela de rutare
rtable search(rtable v[], uint32_t ip, int n) {
	int s = 0, e = n;
	while(s != e) {
		if((v[(s + e) / 2].masca.s_addr & ip) == v[(s + e) / 2].prefix.s_addr) {
			int m = ((s + e) / 2) + 1, c = (s + e) / 2;
			while((v[m].masca.s_addr & ip) == v[m].prefix.s_addr) {
				if(v[m].masca.s_addr > v[c].masca.s_addr){
					c = m;
				}
				m++;
			}
			return v[c];
		} else {
			if((v[(s + e) / 2].masca.s_addr & ip) > v[(s + e) / 2].prefix.s_addr) {
				s = (s + e) / 2 + 1;
			} else {
				e = (s + e) / 2;
			}
		}
	}
	rtable aux;
	aux.prefix.s_addr = 0;
	aux.masca.s_addr = 0;
	aux.next_hop.s_addr = 0;
	aux.interfata = -1;
	return aux;
}

//funtie de parsare a tabelei de rutare
void parseRT(rtable v[], int nr) {
	char *p = (char*)malloc(sizeof(char)*40), *n = (char*)malloc(sizeof(char)*40), *m = (char*)malloc(sizeof(char)*40);
	int i;
	FILE *file = fopen("rtable.txt", "r");
	for(i = 0;i < nr;i++) {
		fscanf(file, "%s %s %s %d", p, n, m, &v[i].interfata);
		inet_aton(p, &v[i].prefix);
		inet_aton(n, &v[i].next_hop);
		inet_aton(m, &v[i].masca);
	}
	free(p);
	free(n);
	free(m);
	fclose(file);
}

//functie de gasire a elementului dorit din arp_table
arpTable* find(List ar, uint32_t ip) {
	while(ar != NULL) {
		if(ar -> info.ip == ip)
			return &ar -> info;
		ar = ar -> next;
	}
	return NULL;
}

//structura pentru retinerea pachetelor in coada de asteptare
typedef struct {
	packet p;
	int interfata;
	uint32_t next_hop;
} waiting_packet;

//funtia de calculare checksum din laborator
uint16_t checksum(void *vdata, size_t length) {

	char* data=(char*)vdata;
	uint64_t acc=0xffff;

	unsigned int offset=((uintptr_t)data)&3;
	if (offset) {
		size_t count=4-offset;
		if (count>length) count=length;
		uint32_t word=0;
		memcpy(offset+(char*)&word,data,count);
		acc+=ntohl(word);
		data+=count;
		length-=count;
	}

	char* data_end=data+(length&~3);
	while (data!=data_end) {
		uint32_t word;
		memcpy(&word,data,4);
		acc+=ntohl(word);
		data+=4;
	}
	length&=3;

	if (length) {
		uint32_t word=0;
		memcpy(&word,data,length);
		acc+=ntohl(word);
	}
	acc=(acc&0xffffffff)+(acc>>32);
	while (acc>>16) {
		acc=(acc&0xffff)+(acc>>16);
	}
	if (offset&1) {
		acc=((acc&0xff00)>>8)|((acc&0x00ff)<<8);
	}
	return htons(~acc);
}

//funtie de cautare in coada a pachetelor ce au ip-ul primit in arp_reply si trimitere a acestora
void try_send_pkg(queue waiting, uint32_t ip, unsigned char new_mac[6]) {
	queue aux = queue_create();
	waiting_packet* p;
	while(!queue_empty(waiting)) {
		p = queue_deq(waiting);
		if(p -> next_hop == ip) {
			struct iphdr *iph = (struct iphdr*)(p -> p.payload + sizeof(struct ether_header));
			struct ether_header *eth = (struct ether_header*)p -> p.payload;
			unsigned char mac[6];
			get_interface_mac(p -> interfata, mac);
			memcpy(eth -> ether_shost, mac, 6);
			memcpy(eth -> ether_dhost, new_mac, 6);
			p -> p.len = sizeof(struct ether_header) + ntohs(iph -> tot_len);
			iph -> ttl -= 1;
			iph -> check = checksum(iph, sizeof(struct iphdr));
			send_packet(p -> interfata, &p -> p);		
		} else {
			queue_enq(aux, p);
		}
	}
	while(!queue_empty(aux)){
		p = queue_deq(aux);
		queue_enq(waiting, p);
	}
}

int main(int argc, char *argv[])
{
	packet m;
	int rc;
	int nr = count();
	rtable vect[nr];
	parseRT(vect, nr);
	mergeSort(vect, 0, nr - 1);
	init();
	List tab_arp = NULL;
	arpTable* arp_poz;
	queue wainting_queue = queue_create () ;

	while (1) {
		rc = get_packet(&m);
		DIE(rc < 0, "get_message");
		/* Students will write code here */
		struct ether_header *eth = (struct ether_header*)m.payload;
		if(eth->ether_type == htons(0x0806)) {
			//e ARP
			struct ether_arp *arp = (struct ether_arp*)(m.payload + sizeof(struct ether_header));
			if(htons(arp->ea_hdr.ar_op) == 1) {
				//am primit ARP request
				memcpy(eth->ether_dhost, eth->ether_shost, 6);
				unsigned char mac[6];
				get_interface_mac(m.interface, mac);
				memcpy(eth->ether_shost, mac, 6);

				arp->ea_hdr.ar_op = htons(2);
				memcpy(arp->arp_tha, arp->arp_sha, 6);
				memcpy(arp->arp_tpa, arp->arp_spa, 4);
				memcpy(arp->arp_sha, mac, 6);
				struct in_addr ad;
				inet_aton(get_interface_ip(m.interface), &ad);
				memcpy(arp->arp_spa, &ad.s_addr, 4);

				send_packet(m.interface, &m);
			} else {
				//am primit ARP reply
				arpTable info;
				memcpy(&info.ip, arp -> arp_spa, 4);
				memcpy(info.mac, arp -> arp_sha, 6);
				addList(&tab_arp, info);
				try_send_pkg(wainting_queue, info.ip, info.mac);
			}
		} else {
			//e IP
			struct iphdr *iphd = (struct iphdr*)(m.payload + sizeof(struct ether_header));
			struct in_addr my_ip;
			if(iphd -> ttl <= 1) {
				//trimit ICMP timeout
				memcpy(m.payload + sizeof(struct ether_header) + sizeof(struct iphdr) + sizeof(struct icmphdr), iphd, sizeof(struct iphdr));
				m.len = sizeof(struct ether_header) + 2 * sizeof(struct iphdr) + sizeof(struct icmphdr);
				struct icmphdr *icmp = (struct icmphdr*)(m.payload + sizeof(struct ether_header) + sizeof(struct iphdr));
				iphd -> tot_len = m.len - sizeof(struct ether_header);
				iphd -> daddr = iphd -> saddr;
				iphd -> saddr = my_ip.s_addr;
				memcpy(eth -> ether_dhost, eth -> ether_shost, 6);
				unsigned char new_mac[6];
				get_interface_mac(m.interface, new_mac);
				memcpy(eth -> ether_shost, new_mac, 6);
				icmp -> type = 11;
				icmp -> code = 0;
				iphd -> protocol = 1;
				iphd -> check = 0;
				iphd -> check = checksum(iphd, sizeof(struct iphdr));
				icmp -> checksum = 0;
				icmp -> checksum = checksum(icmp, m.len - sizeof(struct ether_header) - sizeof(struct iphdr));
				send_packet(m.interface, &m);
			} else {
				int check = iphd -> check;
				iphd -> check = 0;
				if(checksum(iphd, sizeof(struct iphdr)) == check) {
					inet_aton(get_interface_ip(m.interface), &my_ip);
					if (iphd -> daddr != my_ip.s_addr) {
						rtable poz = search(vect, iphd->daddr, nr);
						if(poz.interfata != -1) {
							if(poz.next_hop.s_addr == iphd->daddr) {
								arp_poz = find(tab_arp, poz.next_hop.s_addr);
								if(arp_poz != NULL) {
									iphd -> ttl -= 1; 	
									unsigned char mac[6];
									get_interface_mac(m.interface, mac);
									memcpy(eth -> ether_shost, mac, 6);
									memcpy(eth -> ether_dhost, arp_poz -> mac, 6);
									iphd -> check = checksum(iphd, sizeof(struct iphdr));
									send_packet(poz.interfata, &m); 
								} else {
									//fac arp request si adaug pachetul in coada de asteptare
									waiting_packet p;
									p.p = m;
									p.interfata = poz.interfata;
									p.next_hop = poz.next_hop.s_addr;
									queue_enq(wainting_queue, &p);
									unsigned char new_mac[6];
									get_interface_mac(poz.interfata, new_mac);
									inet_aton(get_interface_ip(poz.interfata), &my_ip);
									packet new;
									struct ether_header *eth_new = (struct ether_header*)new.payload;
									struct ether_arp *arp_new = (struct ether_arp*)(new.payload + sizeof(struct ether_header));
									memcpy(eth_new -> ether_shost, new_mac, 6);
									unsigned char broadcast[6];
									hwaddr_aton("ff:ff:ff:ff:ff:ff", broadcast);
									memcpy(eth_new -> ether_dhost, broadcast, 6);
									eth_new -> ether_type = htons(0x0806);
									arp_new -> ea_hdr.ar_hrd = htons(1);
									arp_new -> ea_hdr.ar_pro = htons(0x0800);
									arp_new -> ea_hdr.ar_hln = 6;
									arp_new -> ea_hdr.ar_pln = 4;
									arp_new -> ea_hdr.ar_op = htons(1);
									memcpy(arp_new->arp_sha, new_mac, 6);
									memcpy(arp_new -> arp_spa, &my_ip.s_addr, 4);
									memcpy(arp_new -> arp_tha, broadcast, 6);
									memcpy(arp_new -> arp_tpa, &poz.next_hop.s_addr, 4);
									new.interface = poz.interfata;
									new.len = sizeof(struct ether_header) + sizeof(struct ether_arp);
									send_packet(new.interface, &new);
								}
							} else 
								DIE(1, "gresit");
						} else{
							// trimit ICMP destination unreachable
							memcpy(m.payload + sizeof(struct ether_header) + sizeof(struct iphdr) + sizeof(struct icmphdr), iphd, sizeof(struct iphdr));
							m.len = sizeof(struct ether_header) + 2 * sizeof(struct iphdr) + sizeof(struct icmphdr);
							struct icmphdr *icmp = (struct icmphdr*)(m.payload + sizeof(struct ether_header) + sizeof(struct iphdr));
							iphd -> tot_len = m.len - sizeof(struct ether_header);
							iphd -> daddr = iphd -> saddr;
							iphd -> saddr = my_ip.s_addr;
							memcpy(eth -> ether_dhost, eth -> ether_shost, 6);
							unsigned char new_mac[6];
							get_interface_mac(m.interface, new_mac);
							memcpy(eth -> ether_shost, new_mac, 6);
							icmp -> type = 3;
							icmp -> code = 0;
							iphd -> protocol = 1;
							iphd -> check = 0;
							iphd -> check = checksum(iphd, sizeof(struct iphdr));
							icmp -> checksum = 0;
							icmp -> checksum = checksum(icmp, m.len - sizeof(struct ether_header) - sizeof(struct iphdr));
							send_packet(m.interface, &m);
						}
					} else {
						//trimit icmp echo reply
						struct icmphdr *icmp = (struct icmphdr*)(m.payload + sizeof(struct ether_header) + sizeof(struct iphdr));
						iphd -> daddr = iphd -> saddr;
						iphd -> saddr = my_ip.s_addr;
						memcpy(eth -> ether_dhost, eth -> ether_shost, 6);
						unsigned char new_mac[6];
						get_interface_mac(m.interface, new_mac);
						memcpy(eth -> ether_shost, new_mac, 6);
						icmp -> type = 0;
						iphd -> check = 0;
						iphd -> check = checksum(iphd, sizeof(struct iphdr));
						icmp -> checksum = 0;
						icmp -> checksum = checksum(icmp, m.len - sizeof(struct ether_header) - sizeof(struct iphdr));
						send_packet(m.interface, &m);
					}
				}
			}
		}
	}
}