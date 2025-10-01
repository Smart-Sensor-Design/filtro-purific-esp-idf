#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <inttypes.h>
#include <stdbool.h>
#include <time.h>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/event_groups.h"
#include "freertos/semphr.h"

#include "esp_system.h"
#include "esp_mac.h"   // for esp_read_mac() and ESP_MAC_WIFI_STA
#include "esp_chip_info.h"
#include "esp_event.h"
#include "esp_log.h"
#include "esp_timer.h"
#include "esp_wifi.h"
#include "esp_netif.h"
#include "nvs_flash.h"
#include "nvs.h"

#include "esp_sntp.h"
#include "mdns.h"

#include "esp_adc/adc_oneshot.h"
#include "mqtt_client.h"
#include "esp_http_client.h"

#include "driver/gpio.h"
#define TDS_GPIO               GPIO_NUM_1     // Entrada analógica para TDS (qualidade da água)

#include "esp_https_ota.h"
#include "esp_ota_ops.h"
#include "esp_crt_bundle.h"
// HTTP server for custom captive portal (attached to provisioning server)
#include "esp_http_server.h"
// lwIP (DNS server + sockets)
#include "lwip/sockets.h"
#include "lwip/ip4_addr.h"
#include "lwip/inet.h"

// ========================= Config =========================
#define FIRMWARE_VERSION "3.2.5"
#define URL_ADD_TDS                     "https://smartsensordesign.xyz/flowhall/api/add-tds"

// Wi-Fi credentials now provided only via BLE provisioning (no hardcoded defaults)
static double s_tds_value = 0.0; // último TDS calculado
static bool   s_tds_valid = false; // true se houve leitura TDS recente



// New board pin mapping (added for valve stepper control) from Arduino reference:
// IO1  -> TDS (analog) (if used later)
// IO11 -> WIFI RESET BUTTON (already using GPIO0 in legacy build; keep mapping but define symbolic new pin for clarity)
// IO13 -> HALL SENSOR (new hall position, will still keep legacy HALL_GPIO usage for existing flow sensor to avoid breaking behavior)
// IO18 -> FLP (reserved)
// IO19 -> RST/SLP COLD valve stepper driver
// IO20 -> STEP shared
// IO21 -> DIR shared
// IO22 -> EN shared (active low)
// IO23 -> RST/SLP NATURAL valve stepper driver

#define PIN_TDS_GPIO              GPIO_NUM_1
#define PIN_WIFI_RESET_NEW        GPIO_NUM_11
#define PIN_HALL_NEW              GPIO_NUM_13
#define PIN_FLP                   GPIO_NUM_18
#define PIN_RSTSLP_COLD           GPIO_NUM_19
#define PIN_STEP_SHARED           GPIO_NUM_20
#define PIN_DIR_SHARED            GPIO_NUM_21
#define PIN_ENABLE_SHARED         GPIO_NUM_22
#define PIN_RSTSLP_NAT            GPIO_NUM_23
#define WIFI_RESET_GPIO            PIN_WIFI_RESET_NEW   // Legacy name now points to new pin IO11
#define HALL_GPIO                  PIN_HALL_NEW         // Legacy name now points to new hall sensor IO13
#define FLOW_SAMPLE_MS          100   // calcular fluxo a cada 100ms
// URLs
#define URL_DEVICE_IP                  "https://smartsensordesign.xyz/flowhall/api/device-ip"
#define URL_REPORT_FIRMWARE_VERSION    "https://smartsensordesign.xyz/flowhall/api/report-firmware-version"
#define URL_ADD_READING                "https://smartsensordesign.xyz/flowhall/api/add-reading"
#define URL_GET_CALIBRATION_FACTOR     "https://smartsensordesign.xyz/flowhall/api/get-calibration-factor"
#define URL_DOWNLOAD_FIRMWARE          "https://smartsensordesign.xyz/flowhall/api/download-firmware"

// MQTT
#define MQTT_BROKER        "82.29.57.196"
#define MQTT_PORT          1883
#define MQTT_USER          "esp32_user"
#define MQTT_PASSWORD      "esp32pass"

// Timing
#define HEARTBEAT_INTERVAL_MS   30000
#define SEND_INTERVAL_MS        3000
// Network failure watchdog: if multiple failures happen in a short window, open portal
#define NET_FAIL_WINDOW_MS       30000
#define NET_FAIL_THRESHOLD       4

// ==========================================================

static const char* TAG = "FLOW_HALL";

static EventGroupHandle_t s_wifi_event_group;
#define WIFI_CONNECTED_BIT BIT0

// Track Wi-Fi stability / portal state
static int s_wifi_disconnects = 0;
static bool s_portal_active = false;
static bool s_portal_recovery = false; // after submit, re-show portal on first failure
static void start_portal(void);
static void stop_portal(void);
static bool have_sta_creds(void);
// STA reconnect pacing and timer
static uint64_t s_last_sta_connect_ms = 0;
static esp_timer_handle_t s_sta_reconnect_timer = NULL;
static void sta_reconnect_cb(void* arg);
// Connectivity watchdog state
static int s_net_failures = 0;
static uint64_t s_net_first_fail_ms = 0;

// (Old provisioning forward decls removed)

// ================= Captive portal (custom HTML form) =================
// Very small inline page (keep size minimal). You can style further if flash allows.
static const char *CAPTIVE_FORM_HTML =
"<!DOCTYPE html><html><head><meta name=viewport content='width=device-width,initial-scale=1'>"
"<title>Config Wi-Fi</title><style>body{font-family:Arial;margin:24px;background:#f2f2f2;}*{box-sizing:border-box}"
"h1{font-size:18px;}form{background:#fff;padding:16px;border-radius:8px;box-shadow:0 2px 4px #0002;}"
"label{display:block;margin-top:12px;font-weight:600;}input{width:100%;padding:8px;margin-top:4px;}"
"button{margin-top:16px;padding:10px 14px;background:#1976d2;color:#fff;border:0;border-radius:4px;font-size:14px;}"
".msg{color:#d32;margin-top:12px;font-size:13px;}"
".net{list-style:none;padding:0;margin:16px 0;} .net li{background:#fff;margin:6px 0;padding:10px;border-radius:8px;box-shadow:0 1px 3px #0002;display:flex;justify-content:space-between;align-items:center;cursor:pointer;}"
".sec{font-size:12px;color:#555;margin-left:8px;} .rssi{font-size:12px;color:#333;} .row{display:flex;gap:8px;align-items:center;}"
".actions{display:flex;gap:8px;align-items:center;margin-top:8px;} .btn{background:#555;color:#fff;border:0;border-radius:4px;padding:6px 10px;cursor:pointer;} .btn:disabled{opacity:.6;cursor:default;}"
".pw-wrap{display:flex;align-items:center;gap:8px;} .pw-wrap input{flex:1;min-width:0;} .pw-toggle{flex:0 0 auto;background:#1976d2;color:#fff;border:0;border-radius:6px;padding:6px 10px;font-size:12px;cursor:pointer;line-height:1;display:inline-flex;align-items:center;justify-content:center;height:34px;} .pw-toggle:active{transform:scale(.98);}"
"</style></head><body>"
"<h1>Configurar Wi‑Fi</h1>"
"<form method=POST action='/submit' onsubmit=\"document.getElementById('submitBtn').disabled=true;\">"
"<label>SSID<input id=ssid name=ssid maxlength=32 required></label>"
"<label>Senha<div class='pw-wrap'><input id=password name=password type=password maxlength=64 autocomplete='current-password'><button id=pwToggle class='pw-toggle' type=button>Mostrar</button></div></label>"
"<button id=submitBtn type=submit>Salvar & Conectar</button>"
"<p class=msg>Escolha a rede abaixo para preencher o SSID automaticamente.</p>"
"</form>"
"<div class=actions><button id=refresh class=btn>Atualizar lista</button><span id=scanStatus></span></div>"
"<ul id=networks class=net></ul>"
"<script>"
"const ssidEl=document.getElementById('ssid'); const passEl=document.getElementById('password'); const ul=document.getElementById('networks'); const stat=document.getElementById('scanStatus');"
"const pwBtn=document.getElementById('pwToggle'); if(pwBtn){pwBtn.onclick=(e)=>{e.preventDefault(); if(passEl.type==='password'){passEl.type='text'; pwBtn.textContent='Ocultar';} else {passEl.type='password'; pwBtn.textContent='Mostrar';}};}"
"function secName(a){return ({0:'OPEN',1:'WEP',2:'WPA_PSK',3:'WPA2_PSK',4:'WPA_WPA2',5:'WPA2_ENTER',6:'WPA3_PSK',7:'WPA2_WPA3'})[a]||'?' }"
"function fillList(list){ ul.innerHTML=''; if(!Array.isArray(list)||!list.length){ ul.innerHTML='<li>Nenhuma rede encontrada</li>'; return;} list.forEach(ap=>{ if(!ap.ssid) return; const li=document.createElement('li'); li.onclick=()=>{ ssidEl.value=ap.ssid; passEl.focus(); window.scrollTo({top:0,behavior:'smooth'}); }; const left=document.createElement('div'); left.className='row'; left.textContent=ap.ssid; const sec=document.createElement('span'); sec.className='sec'; sec.textContent=' '+secName(ap.authmode); left.appendChild(sec); const rssi=document.createElement('div'); rssi.className='rssi'; rssi.textContent=ap.rssi+' dBm'; li.appendChild(left); li.appendChild(rssi); ul.appendChild(li); }); }"
"async function loadScan(){ try{ stat.textContent='Procurando redes...'; const r=await fetch('/scan'); const j=await r.json(); fillList(j); stat.textContent=''; }catch(e){ stat.textContent='Falha ao procurar redes'; }}"
"document.getElementById('refresh').onclick=(e)=>{ e.preventDefault(); loadScan(); };"
"document.addEventListener('DOMContentLoaded',()=>{ loadScan(); });"
"</script>"
"</body></html>";


static httpd_handle_t s_captive_httpd = NULL; // custom http server shared with provisioning
static TaskHandle_t s_dns_task = NULL;       // captive DNS server task
static volatile bool s_dns_stop = false;
// Captive scan task state
static TaskHandle_t s_scan_task = NULL;
static volatile bool s_scan_stop = false;
static volatile bool s_scan_request = false; // request immediate scan
static char s_scan_json[2048] = "[]"; // cached scan result JSON
static uint64_t s_scan_last_ms = 0;
static void scan_captive_task(void* pv) {
    const TickType_t interval = pdMS_TO_TICKS(7000);
    for (;;) {
        if (s_scan_stop) break;
        uint64_t now = (uint64_t)(esp_timer_get_time()/1000ULL);
        bool do_scan = s_scan_request || (now - s_scan_last_ms > 12000);
        s_scan_request = false;
        if (do_scan && s_portal_active) {
            wifi_scan_config_t sc = {0};
            sc.show_hidden = false;
            sc.scan_type = WIFI_SCAN_TYPE_PASSIVE;
            sc.scan_time.passive = 60; // ms per channel
            (void)esp_wifi_scan_stop();
            if (esp_wifi_scan_start(&sc, true) == ESP_OK) {
                uint16_t num = 0;
                esp_wifi_scan_get_ap_num(&num);
                if (num > 24) num = 24;
                wifi_ap_record_t *recs = NULL;
                if (num > 0) {
                    recs = (wifi_ap_record_t*)calloc(num, sizeof(wifi_ap_record_t));
                    if (recs) esp_wifi_scan_get_ap_records(&num, recs);
                }
                char buf[sizeof(s_scan_json)]; size_t off = 0; buf[0] = '['; off=1;
                for (uint16_t i=0; i<num; ++i) {
                    const wifi_ap_record_t* r=&recs[i];
                    char ssid_esc[2*33]; size_t se=0;
                    for (int k=0; k<32 && r->ssid[k]; ++k) {
                        char c=r->ssid[k];
                        if (c=='"' || c=='\\') { if (se < sizeof(ssid_esc)-2) { ssid_esc[se++]='\\'; ssid_esc[se++]=c; } }
                        else { if (se < sizeof(ssid_esc)-1) ssid_esc[se++]=c; }
                    }
                    if (se < sizeof(ssid_esc)) ssid_esc[se]=0;
                    int n = snprintf(buf+off, (off<sizeof(buf)? sizeof(buf)-off:0), "%s{\"ssid\":\"%s\",\"rssi\":%d,\"authmode\":%d}",
                                     (i?",":""), ssid_esc, (int)r->rssi, (int)r->authmode);
                    if (n > 0) {
                        off += (size_t)n;
                    }
                    if (off >= sizeof(buf) - 2) {
                        off = sizeof(buf) - 2;
                        break;
                    }
                }
                if (off < sizeof(buf) - 1) {
                    buf[off++] = ']';
                }
                buf[off] = 0;
                strncpy(s_scan_json, buf, sizeof(s_scan_json)-1); s_scan_json[sizeof(s_scan_json)-1]=0;
                if (recs) free(recs);
                s_scan_last_ms = (uint64_t)(esp_timer_get_time()/1000ULL);
            }
        }
        vTaskDelay(interval);
    }
    s_scan_task = NULL; vTaskDelete(NULL);
}

// Parse very small application/x-www-form-urlencoded body (ssid=..&password=..)
static void url_decode_inplace(char *s) {
    char *o = s; char hex[3]={0};
    while (*s) {
        if (*s=='+' ) { *o++=' '; s++; }
        else if (*s=='%' && s[1] && s[2]) { hex[0]=s[1]; hex[1]=s[2]; *o++=(char)strtol(hex,NULL,16); s+=3; }
        else { *o++=*s++; }
    }
    *o=0;
}

static esp_err_t root_get_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "text/html; charset=utf-8");
    return httpd_resp_send(req, CAPTIVE_FORM_HTML, HTTPD_RESP_USE_STRLEN);
}

static esp_err_t submit_post_handler(httpd_req_t *req) {
    char buf[256]; int total = req->content_len; if (total >= (int)sizeof(buf)) total = sizeof(buf)-1; int r= httpd_req_recv(req, buf, total); if (r<=0) return httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "recv fail"); buf[r]=0;
    char ssid[33]={0}, pass[65]={0};
    // crude parsing
    char *p = buf; while (p && *p) {
        char *pair = p; char *amp = strchr(pair,'&'); if (amp) *amp=0; p = amp ? amp+1 : NULL; char *eq = strchr(pair,'='); if (!eq) continue; *eq=0; char *k=pair; char *v=eq+1; url_decode_inplace(k); url_decode_inplace(v); if (strcmp(k,"ssid")==0) strlcpy(ssid,v,sizeof(ssid)); else if (strcmp(k,"password")==0) strlcpy(pass,v,sizeof(pass)); }
    if (strlen(ssid)==0) {
        return httpd_resp_send_err(req, HTTPD_400_BAD_REQUEST, "SSID vazio");
    }
    wifi_config_t cfg = {0};
    strlcpy((char*)cfg.sta.ssid, ssid, sizeof(cfg.sta.ssid));
    strlcpy((char*)cfg.sta.password, pass, sizeof(cfg.sta.password));
    ESP_LOGI(TAG, "Captive submit: ssid='%s' pass_len=%d", ssid, (int)strlen(pass));
    // Apply credentials directly; portal will auto-stop after STA gets IP.
    // Keep running in APSTA so this page can load; stop the portal only after a successful STA IP.
    // Arm a quick recovery flag to keep portal visible if the connection fails.
    s_portal_recovery = true;
    s_wifi_disconnects = 0;
    esp_wifi_set_config(WIFI_IF_STA, &cfg);
    // Start/Restart STA connection while AP stays up
    esp_wifi_disconnect();
    esp_wifi_connect();
    // Loading page: show spinner for 15s; if AP still up, inform error and redirect to portal
    httpd_resp_set_type(req, "text/html; charset=utf-8");
    httpd_resp_sendstr(req,
        "<!DOCTYPE html><html><head><meta name=viewport content='width=device-width,initial-scale=1'>"
        "<title>Conectando...</title>"
        "<style>body{margin:0;display:flex;min-height:100vh;align-items:center;justify-content:center;background:#f5f5f5;font-family:Arial}"
        ".card{background:#fff;padding:24px 28px;border-radius:12px;box-shadow:0 6px 24px #0002;max-width:460px;text-align:center}"
        ".sp{width:72px;height:72px;border:8px solid #e0e0e0;border-top-color:#1976d2;border-radius:50%;animation:rot 1s linear infinite;margin:12px auto 16px}"
        "@keyframes rot{to{transform:rotate(360deg)}}"
        ".muted{color:#666;font-size:13px;margin-top:8px}"
        "a.btn{display:inline-block;margin-top:16px;padding:10px 14px;background:#1976d2;color:#fff;text-decoration:none;border-radius:8px}"
        "</style></head><body>"
        "<div class=card>"
        "<div class=sp></div>"
        "<h2>Aguarde...</h2>"
        "<p id=msg>Estamos conectando o dispositivo ao seu Wi‑Fi.</p>"
        "<p class=muted>Esta tela deve fechar automaticamente assim que o dispositivo se conectar.</p>"
        "<a class=btn href='http://192.168.4.1/'>Voltar ao portal agora</a>"
        "</div>"
        "<script>setTimeout(function(){var m=document.getElementById('msg');m.textContent='Não foi possível conectar. Voltando ao portal para revisar as credenciais...';setTimeout(function(){location.href='http://192.168.4.1/';},1500);},20000);</script>"
        "</body></html>");
    return ESP_OK;
}

static const char* authmode_to_str(wifi_auth_mode_t m) {
    switch (m) {
        case WIFI_AUTH_OPEN: return "OPEN";
        case WIFI_AUTH_WEP: return "WEP";
        case WIFI_AUTH_WPA_PSK: return "WPA_PSK";
        case WIFI_AUTH_WPA2_PSK: return "WPA2_PSK";
        case WIFI_AUTH_WPA_WPA2_PSK: return "WPA_WPA2";
        case WIFI_AUTH_WPA2_ENTERPRISE: return "WPA2_ENTER";
        case WIFI_AUTH_WPA3_PSK: return "WPA3_PSK";
        case WIFI_AUTH_WPA2_WPA3_PSK: return "WPA2_WPA3";
        default: return "UNKNOWN";
    }
}

static esp_err_t scan_get_handler(httpd_req_t *req) {
    // Serve cached scan JSON immediately to keep the portal stable
    httpd_resp_set_type(req, "application/json");
    httpd_resp_sendstr(req, s_scan_json[0] ? s_scan_json : "[]");
    // Hint background task to refresh soon
    s_scan_request = true;
    // While the portal is active we still want to keep STA reconnect attempts alive so that
    // if the original network returns the device auto-recovers without user action.
    if (s_portal_active && have_sta_creds()) {
        uint64_t now_ms = (uint64_t)(esp_timer_get_time()/1000ULL);
        if (s_last_sta_connect_ms == 0 || (now_ms - s_last_sta_connect_ms) >= 3000) {
            ESP_LOGI(TAG, "Portal scan hit: attempting background STA reconnect");
            esp_wifi_connect();
            s_last_sta_connect_ms = now_ms;
        }
    }
    return ESP_OK;
}

// ---- Captive portal helpers (auto popup on iOS/Android/Windows) ----
static void get_ap_ip_str(char out[16]) {
    out[0] = '\0';
    esp_netif_t* ap = esp_netif_get_handle_from_ifkey("WIFI_AP_DEF");
    if (!ap) { strcpy(out, "192.168.4.1"); return; }
    esp_netif_ip_info_t ip;
    if (esp_netif_get_ip_info(ap, &ip) == ESP_OK) {
        sprintf(out, IPSTR, IP2STR(&ip.ip));
    } else {
        strcpy(out, "192.168.4.1");
    }
}

static esp_err_t captive_redirect_handler(httpd_req_t* req) {
    char ip[16];
    get_ap_ip_str(ip);
    char redirect_html[200];  // Slightly larger buffer for safety
    snprintf(redirect_html, sizeof(redirect_html),
             "<!DOCTYPE html><html><head>"
             "<meta http-equiv=\"refresh\" content=\"0; url=http://%s/\">"
             "<title>Redirecting...</title></head>"
             "<body>Redirecting to configuration portal...</body></html>",
             ip);
    httpd_resp_set_type(req, "text/html; charset=utf-8");
    httpd_resp_set_hdr(req, "Cache-Control", "no-cache, no-store, must-revalidate");
    httpd_resp_set_hdr(req, "Pragma", "no-cache");
    httpd_resp_set_hdr(req, "Expires", "0");
    httpd_resp_set_hdr(req, "Connection", "close");
    return httpd_resp_send(req, redirect_html, strlen(redirect_html));
}

// Minimal DNS server: respond to any query with A record pointing to AP IP
typedef struct __attribute__((packed)) {
    uint16_t id;
    uint16_t flags;
    uint16_t qdcount;
    uint16_t ancount;
    uint16_t nscount;
    uint16_t arcount;
} dns_hdr_t;

static void dns_server_task(void* pv) {
    int sock = -1;
    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_port = htons(53);
    addr.sin_addr.s_addr = htonl(INADDR_ANY);

    sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
    if (sock < 0) {
        ESP_LOGE(TAG, "DNS: socket() failed");
        vTaskDelete(NULL);
        return;
    }
    int yes = 1; setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(yes));
    struct timeval tv = { .tv_sec = 0, .tv_usec = 200000 }; // 200ms
    setsockopt(sock, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    if (bind(sock, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
        ESP_LOGE(TAG, "DNS: bind() failed");
        close(sock);
        vTaskDelete(NULL);
        return;
    }

    char ap_ip_str[16];
    get_ap_ip_str(ap_ip_str);
    uint32_t ap_ip_be = inet_addr(ap_ip_str); // already BE
    ESP_LOGI(TAG, "DNS: captive server up, answering with %s", ap_ip_str);

    while (!s_dns_stop) {
        uint8_t buf[512];
        struct sockaddr_in src; socklen_t sl = sizeof(src);
        int n = recvfrom(sock, buf, sizeof(buf), 0, (struct sockaddr*)&src, &sl);
        if (n < (int)sizeof(dns_hdr_t)) continue;

        dns_hdr_t* h = (dns_hdr_t*)buf;
        uint16_t qd = ntohs(h->qdcount);
        if (qd == 0) continue;

        // Build response in-place
        uint16_t id = h->id;
        // Flags: QR=1, OPCODE=0, AA=1, TC=0, RD=copy, RA=0, Z=0, RCODE=0 => 0x8180 w/ RD bit preserved
        uint16_t rd = ntohs(h->flags) & 0x0100; // RD
        h->id = id;
        h->flags = htons(0x8180 | rd);
        h->ancount = htons(1);
        h->nscount = 0;
        h->arcount = 0;

        // Find end of first question
        int pos = sizeof(dns_hdr_t);
        while (pos < n && buf[pos] != 0) {
            uint8_t l = buf[pos];
            if ((l & 0xC0) == 0xC0) { pos += 2; break; } // compression (unlikely in query)
            pos += 1 + l;
        }
        if (pos >= n) continue;
        pos++; // skip null label
        if (pos + 4 > n) continue; // QTYPE+QCLASS present
        int qend = pos + 4;

        uint16_t qtype = ntohs(*(uint16_t *)(buf + qend - 4));
        if (qtype != 1) {  // Not A record query
            // Set authoritative response with no answer
            h->flags = htons(0x8180 | rd);
            h->ancount = htons(0);
            h->qdcount = htons(1);
            // Send back header + question only
            sendto(sock, buf, qend, 0, (struct sockaddr*)&src, sl);
            continue;
        }

        // Prepare answer at end of question
        int ans = qend;
        if (ans + 16 > (int)sizeof(buf)) continue; // ensure space
        buf[ans + 0] = 0xC0; buf[ans + 1] = 0x0C; // name pointer to offset 12
        buf[ans + 2] = 0x00; buf[ans + 3] = 0x01; // TYPE=A
        buf[ans + 4] = 0x00; buf[ans + 5] = 0x01; // CLASS=IN
        buf[ans + 6] = 0x00; buf[ans + 7] = 0x00; buf[ans + 8] = 0x00; buf[ans + 9] = 0x3C; // TTL=60s
        buf[ans + 10] = 0x00; buf[ans + 11] = 0x04; // RDLENGTH=4
        memcpy(&buf[ans + 12], &ap_ip_be, 4);
        int resp_len = ans + 16;

        // Ensure qdcount=1 in header (some clients send more; we answer once)
        h->qdcount = htons(1);
        h->flags = htons(0x8180 | rd);
        h->ancount = htons(1);
        sendto(sock, buf, resp_len, 0, (struct sockaddr*)&src, sl);
    }

    ESP_LOGI(TAG, "DNS: captive server stopping");
    if (sock >= 0) close(sock);
    vTaskDelete(NULL);
}

// Persistent URI descriptors (httpd stores pointer; don't use stack-lifetime)
static const httpd_uri_t URI_ROOT = {
    .uri = "/",
    .method = HTTP_GET,
    .handler = root_get_handler,
    .user_ctx = NULL,
};

static const httpd_uri_t URI_SUBMIT = {
    .uri = "/submit",
    .method = HTTP_POST,
    .handler = submit_post_handler,
    .user_ctx = NULL,
};

static const httpd_uri_t URI_SCAN = {
    .uri = "/scan",
    .method = HTTP_GET,
    .handler = scan_get_handler,
    .user_ctx = NULL,
};

static void start_captive_httpd(void) {
    if (s_captive_httpd) return;
    httpd_config_t cfg = HTTPD_DEFAULT_CONFIG();
    cfg.max_uri_handlers = 8;
    // Give httpd a bit more stack to accommodate JSON/scan handlers
    if (cfg.stack_size < 6144) cfg.stack_size = 6144;
    // Enable wildcard match for a catch-all redirect handler registered last
    cfg.uri_match_fn = httpd_uri_match_wildcard;
    if (httpd_start(&s_captive_httpd, &cfg) == ESP_OK) {
        httpd_register_uri_handler(s_captive_httpd, &URI_ROOT);
        httpd_register_uri_handler(s_captive_httpd, &URI_SUBMIT);
    httpd_register_uri_handler(s_captive_httpd, &URI_SCAN);
    // Captive probes -> redirect to /
    static const httpd_uri_t URI_GEN204 = { .uri = "/generate_204", .method = HTTP_GET, .handler = captive_redirect_handler };
    static const httpd_uri_t URI_GEN204_ALT = { .uri = "/gen_204", .method = HTTP_GET, .handler = captive_redirect_handler };
    static const httpd_uri_t URI_APPLE = { .uri = "/hotspot-detect.html", .method = HTTP_GET, .handler = captive_redirect_handler };
    static const httpd_uri_t URI_NCSI = { .uri = "/ncsi.txt", .method = HTTP_GET, .handler = captive_redirect_handler };
    static const httpd_uri_t URI_CONNECTTEST = { .uri = "/connecttest.txt", .method = HTTP_GET, .handler = captive_redirect_handler };
    static const httpd_uri_t URI_FW_LINK = {
        .uri = "/fwlink",
        .method = HTTP_GET,
        .handler = captive_redirect_handler,
        .user_ctx = NULL,
    };
    httpd_register_uri_handler(s_captive_httpd, &URI_GEN204);
    httpd_register_uri_handler(s_captive_httpd, &URI_GEN204_ALT);
    httpd_register_uri_handler(s_captive_httpd, &URI_APPLE);
    httpd_register_uri_handler(s_captive_httpd, &URI_NCSI);
    httpd_register_uri_handler(s_captive_httpd, &URI_CONNECTTEST);
    httpd_register_uri_handler(s_captive_httpd, &URI_FW_LINK);

        // Catch-all redirect for unknown paths (registered last)
        static const httpd_uri_t URI_WILDCARD = { .uri = "/*", .method = HTTP_GET, .handler = captive_redirect_handler };
        httpd_register_uri_handler(s_captive_httpd, &URI_WILDCARD);
        ESP_LOGI(TAG, "Captive HTTP server started (custom handle)");
    } else {
        ESP_LOGE(TAG, "Failed to start captive HTTP server");
    }
}

static void stop_captive_httpd(void) {
    if (s_captive_httpd) {
        httpd_stop(s_captive_httpd);
        s_captive_httpd = NULL;
        ESP_LOGI(TAG, "Captive HTTP server stopped");
    }
}

static bool have_sta_creds(void) {
    wifi_config_t cfg;
    if (esp_wifi_get_config(WIFI_IF_STA, &cfg) == ESP_OK) {
        return cfg.sta.ssid[0] != 0;
    }
    return false;
}

static void start_portal(void) {
    if (s_portal_active) return;
    // AP+STA to host portal while allowing future STA attempts
    esp_wifi_stop();
    esp_wifi_set_mode(WIFI_MODE_APSTA);
    wifi_config_t ap = {0};
    uint8_t mac[6]; esp_read_mac(mac, ESP_MAC_WIFI_STA);
    snprintf((char*)ap.ap.ssid, sizeof(ap.ap.ssid), "FLOWHALL-%02X%02X%02X", mac[3], mac[4], mac[5]);
    ap.ap.ssid_len = strlen((char*)ap.ap.ssid);
    ap.ap.channel = 1;
    ap.ap.max_connection = 4;
    ap.ap.authmode = WIFI_AUTH_OPEN;
    ap.ap.beacon_interval = 100;
    esp_wifi_set_config(WIFI_IF_AP, &ap);
    esp_wifi_start();
    if (have_sta_creds()) {
        esp_wifi_connect();
    }
    start_captive_httpd();
    // Ensure DHCP hands out AP IP as DNS so probes resolve here
    esp_netif_t* ap_netif = esp_netif_get_handle_from_ifkey("WIFI_AP_DEF");
    if (ap_netif) {
        esp_netif_ip_info_t ip;
        if (esp_netif_get_ip_info(ap_netif, &ip) == ESP_OK) {
            ip4_addr_t dns = { .addr = ip.ip.addr };
            esp_netif_dhcps_stop(ap_netif);
            esp_netif_dhcps_option(ap_netif, ESP_NETIF_OP_SET, ESP_NETIF_DOMAIN_NAME_SERVER, &dns, sizeof(dns));
            esp_netif_dhcps_start(ap_netif);
            char portal_url[] = "http://192.168.4.1/";
            esp_netif_dhcps_option(ap_netif, ESP_NETIF_OP_SET, 114, portal_url, strlen(portal_url));
        }
    }
    // Start DNS hijack task
    s_dns_stop = false;
    if (!s_dns_task) xTaskCreate(dns_server_task, "dns_captive", 3072, NULL, 4, &s_dns_task);
    // Start background Wi-Fi scan task to populate /scan cache
    s_scan_stop = false;
    s_scan_request = true; // do an initial scan fast
    if (!s_scan_task) xTaskCreatePinnedToCore(scan_captive_task, "scan_captive", 4096, NULL, 4, &s_scan_task, tskNO_AFFINITY);
    s_portal_active = true;
    ESP_LOGI(TAG, "Portal started SSID=%s", ap.ap.ssid);
}

static void stop_portal(void) {
    if (!s_portal_active) return;
    stop_captive_httpd();
    // Stop DNS hijack task
    s_dns_stop = true;
    if (s_dns_task) {
        // Let task exit via timeout
        vTaskDelay(pdMS_TO_TICKS(250));
        s_dns_task = NULL;
    }
    // Stop scan task
    s_scan_stop = true;
    if (s_scan_task) {
        vTaskDelay(pdMS_TO_TICKS(100));
        s_scan_task = NULL;
    }
    EventBits_t bits = xEventGroupGetBits(s_wifi_event_group);
    if (bits & WIFI_CONNECTED_BIT) {
        esp_wifi_set_mode(WIFI_MODE_STA);
    }
    s_portal_active = false;
}

static esp_mqtt_client_handle_t s_mqtt = NULL;

static char s_mqtt_client_id[64];
static char s_mqtt_topic_geral[64];

static volatile uint64_t s_pulse_count = 0;

static double s_calibration_factor = 0.000554; // pulses to liters (example)
static double s_volume = 0.0;
static double s_volume_last = 0.0;
static double s_fluxo = 0.0;

// ================= Valve / Stepper (new feature integration) =================
// Replicating Arduino logic for dispensing water with timed volume approximation.
// We keep existing telemetry logic intact and just extend MQTT actions.
typedef enum {
    DISPENSE_IDLE = 0,
    DISPENSING_COLD,
    DISPENSING_NATURAL
} dispense_state_t;

static dispense_state_t s_dispense_state = DISPENSE_IDLE;
static uint32_t s_dispense_start_ms = 0;
static int s_dispense_volume_ml = 0;      // requested volume in mL

// Track valve open states (cold / natural) analogous to myPowerState1/2
static bool s_valve_cold_open = false;
static bool s_valve_nat_open  = false;

// Calibration for time-based dispensing (ms per mL) per Arduino reference
static double s_ms_per_ml = 25.2; // can be refined later

// Stepper movement constants (simple open/close symmetric steps)
static const int VALVE_STEPS_OPEN  = 35;
static const int VALVE_STEPS_CLOSE = 35;
static const bool DIR_OPEN_COLD    = true;
static const bool DIR_CLOSE_COLD   = false;
static const bool DIR_OPEN_NAT     = false; // inversion logic retained
static const bool DIR_CLOSE_NAT    = true;

static uint64_t s_last_flow_ms = 0;
static uint64_t s_last_heartbeat_ms = 0;
static uint64_t s_last_send_ms = 0;

typedef struct {
    bool updateCompleted;
    char correlationId[32];
    uint32_t timestamp_ms;
} update_status_t;

static update_status_t s_update_pending = {0};

#ifndef CONFIG_MBEDTLS_CERTIFICATE_BUNDLE
static const char server_root_cert_pem[] =
"-----BEGIN CERTIFICATE-----\n"
"MIIDzTCCA1OgAwIBAgISBcj4hvsg7KX/ybZjNNnUhX+9MAoGCCqGSM49BAMDMDIx\n"
"CzAJBgNVBAYTAlVTMRYwFAYDVQQKEw1MZXQncyBFbmNyeXB0MQswCQYDVQQDEwJF\n"
"NzAeFw0yNTA4MjUyMTQzNTNaFw0yNTExMjMyMTQzNTJaMCAxHjAcBgNVBAMTFXNt\n"
"YXJ0c2Vuc29yZGVzaWduLnh5ejBZMBMGByqGSM49AgEGCCqGSM49AwEHA0IABMe+\n"
"mSpdyVi5HT3cfLpIWGaXsqp66QeS+lmtQFtqt2tpV86jakpd60AD0joFSwz6+SxT\n"
"ZQXAosDGCSJXPEvSw9GjggJZMIICVTAOBgNVHQ8BAf8EBAMCB4AwHQYDVR0lBBYw\n"
"FAYIKwYBBQUHAwEGCCsGAQUFBwMCMAwGA1UdEwEB/wQCMAAwHQYDVR0OBBYEFKKB\n"
"ce1mCWaSDq3AdAkl/VacHUR0MB8GA1UdIwQYMBaAFK5IntyHHUSgb9qi5WB0BHjC\n"
"nACAMDIGCCsGAQUFBwEBBCYwJDAiBggrBgEFBQcwAoYWaHR0cDovL2U3LmkubGVu\n"
"Y3Iub3JnLzBUBgNVHREETTBLghVzbWFydHNlbnNvcmRlc2lnbi54eXqCFnNvdWxk\n"
"aXZpbmVzdGVwcy5jb20uYnKCGnd3dy5zb3VsZGl2aW5lc3RlcHMuY29tLmJyMBMG\n"
"A1UdIAQMMAowCAYGZ4EMAQIBMC0GA1UdHwQmMCQwIqAgoB6GHGh0dHA6Ly9lNy5j\n"
"LmxlbmNyLm9yZy82Mi5jcmwwggEGBgorBgEEAdZ5AgQCBIH3BIH0APIAdwAN4fIw\n"
"K9MNwUBiEgnqVS78R3R8sdfpMO8OQh60fk6qNAAAAZjjZZkbAAAEAwBIMEYCIQCt\n"
"JUZaa3fNjRRwujtMLSY7OH1MgAfvteKBr2zgJ0Qa4QIhAIvTRa81n0nmrzWuUxLv\n"
"eOROjwNyEqMUQKMnDcE1G30xAHcAEvFONL1TckyEBhnDjz96E/jntWKHiJxtMAWE\n"
"6+WGJjoAAAGY42WZGQAABAMASDBGAiEAh4MmqyCFIS/kg8D8yzt0WfZjnrQwdtT9\n"
"MwZXZ6/ADUACIQDrXBYl8/UrqJLt8GxPV8IbOv0UufHRv67HLMYHyaRIrDAKBggq\n"
"hkjOPQQDAwNoADBlAjBQvi+nm26I1zDS28DPjCEXEL6NxtgyRh11MtLVpCK4IxLE\n"
"MDYKpcEG0duUzz6PtHMCMQCWjrulyhruT4dpf9zjqRpwyePzmTEEY0ENlkrwhYBH\n"
"5dDPAZbvi0zP10eqH6+Ea44=\n"
"-----END CERTIFICATE-----\n";
#endif

// ================ Utilities ================

static uint64_t millis64(void) {
    return (uint64_t)(esp_timer_get_time() / 1000ULL);
}

static void mac_to_str(uint8_t mac[6], char* out, size_t out_len, bool colons) {
    if (colons) {
        // Needs 18 bytes including null terminator
        snprintf(out, out_len, "%02X:%02X:%02X:%02X:%02X:%02X",
                 mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
    } else {
        // Needs 13 bytes including null terminator
        snprintf(out, out_len, "%02X%02X%02X%02X%02X%02X",
                 mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
    }
}

static const char* get_chip_model(void) {
    esp_chip_info_t chip_info;
    esp_chip_info(&chip_info);
    switch (chip_info.model) {
        case CHIP_ESP32:   return "ESP32";
        case CHIP_ESP32S2: return "ESP32-S2";
        case CHIP_ESP32S3: return "ESP32-S3";
        case CHIP_ESP32C3: return "ESP32-C3";
        case CHIP_ESP32C2: return "ESP32-C2";
        case CHIP_ESP32C6: return "ESP32-C6";
        case CHIP_ESP32H2: return "ESP32-H2";
        default:           return "Unknown";
    }
}

// ================ NVS (update status) ================

static void save_update_status(const char* correlationId) {
    nvs_handle_t nvs;
    if (nvs_open("update_status", NVS_READWRITE, &nvs) == ESP_OK) {
        nvs_set_u8(nvs, "completed", 1);
        nvs_set_str(nvs, "correlation", correlationId);
        uint32_t now_ms = (uint32_t)millis64();
        nvs_set_u32(nvs, "timestamp", now_ms);
        nvs_commit(nvs);
        nvs_close(nvs);
        ESP_LOGI(TAG, "Saved update status");
    }
}

static void clear_update_status(void) {
    nvs_handle_t nvs;
    if (nvs_open("update_status", NVS_READWRITE, &nvs) == ESP_OK) {
        nvs_erase_all(nvs);
        nvs_commit(nvs);
        nvs_close(nvs);
        ESP_LOGI(TAG, "Cleared update status");
    }
}

static update_status_t get_update_status(void) {
    update_status_t s = {0};
    nvs_handle_t nvs;
    if (nvs_open("update_status", NVS_READONLY, &nvs) == ESP_OK) {
        uint8_t completed = 0;
        size_t len = sizeof(s.correlationId);
        nvs_get_u8(nvs, "completed", &completed);
        nvs_get_str(nvs, "correlation", s.correlationId, &len);
        nvs_get_u32(nvs, "timestamp", &s.timestamp_ms);
        s.updateCompleted = completed != 0;
        nvs_close(nvs);
    }
    return s;
}

// ================ Wi-Fi ================

// Forward declaration: start MQTT after network is up
static void mqtt_init_and_start(void);

static void wifi_event_handler(void* arg, esp_event_base_t base, int32_t id, void* data) {
    // Rate-limit STA reconnect attempts to avoid thrashing while APSTA portal runs
    uint64_t now_ms = (uint64_t)(esp_timer_get_time()/1000ULL);
    if (base == WIFI_EVENT && id == WIFI_EVENT_STA_START) {
        // Always attempt reconnect (also when portal is active) so we auto-recover if Wi‑Fi returns
        if (s_last_sta_connect_ms == 0 || (now_ms - s_last_sta_connect_ms) >= 3000) {
            if (s_portal_active) ESP_LOGI(TAG, "Portal active: attempting STA reconnect");
            esp_wifi_connect();
            s_last_sta_connect_ms = now_ms;
        }
    } else if (base == WIFI_EVENT && id == WIFI_EVENT_STA_DISCONNECTED) {
        wifi_event_sta_disconnected_t* e = (wifi_event_sta_disconnected_t*)data;
        ESP_LOGW(TAG, "WiFi disconnected (reason=%d), handling...", e ? e->reason : -1);
        // Keep trying to reconnect even if the portal is active (background STA attempt)
        uint64_t elapsed = now_ms - s_last_sta_connect_ms;
        if (elapsed >= 3000) {
            if (s_portal_active) ESP_LOGI(TAG, "Portal active: attempting STA reconnect");
            esp_wifi_connect();
            s_last_sta_connect_ms = now_ms;
        } else {
            // Schedule a retry for when the pacing window elapses
            uint64_t delay_ms = 3000 - elapsed;
            if (!s_sta_reconnect_timer) {
                const esp_timer_create_args_t targs = {
                    .callback = sta_reconnect_cb,
                    .arg = NULL,
                    .dispatch_method = ESP_TIMER_TASK,
                    .name = "sta_reconnect"
                };
                if (esp_timer_create(&targs, &s_sta_reconnect_timer) != ESP_OK) {
                    ESP_LOGW(TAG, "Failed to create reconnect timer");
                }
            }
            if (s_sta_reconnect_timer) {
                esp_timer_stop(s_sta_reconnect_timer);
                esp_timer_start_once(s_sta_reconnect_timer, delay_ms * 1000ULL);
                ESP_LOGI(TAG, "Scheduling STA reconnect in %llu ms", (unsigned long long)delay_ms);
            }
        }
        xEventGroupClearBits(s_wifi_event_group, WIFI_CONNECTED_BIT);
        s_wifi_disconnects++;
        // If we just tried new creds from portal and failed, bring portal back immediately and stop reconnect loops
        if (s_portal_recovery) {
            if (!s_portal_active) {
                ESP_LOGW(TAG, "Re-enabling captive portal after failed credentials");
                start_portal();
            }
            s_wifi_disconnects = 0;
        }
        if (s_wifi_disconnects >= 8 && !s_portal_active) {
            ESP_LOGW(TAG, "Too many disconnects (%d) - enabling captive portal", s_wifi_disconnects);
            start_portal();
            s_wifi_disconnects = 0;
        }
    } else if (base == IP_EVENT && id == IP_EVENT_STA_GOT_IP) {
        ip_event_got_ip_t* event = (ip_event_got_ip_t*)data;
        ESP_LOGI(TAG, "Got IP: " IPSTR, IP2STR(&event->ip_info.ip));
        xEventGroupSetBits(s_wifi_event_group, WIFI_CONNECTED_BIT);
        // Reset connectivity watchdog on success
        s_net_failures = 0;
        s_net_first_fail_ms = 0;
        // Stop any pending reconnect timer
        if (s_sta_reconnect_timer) {
            esp_timer_stop(s_sta_reconnect_timer);
        }
        if (s_portal_active) {
            ESP_LOGI(TAG, "STA connected - stopping portal");
            stop_portal();
        }
        // Success path: clear recovery state
        s_portal_recovery = false;
        if (s_mqtt == NULL) {
            mqtt_init_and_start();
        }
        s_wifi_disconnects = 0; // reset on success
    }
}

static void sta_reconnect_cb(void* arg) {
    uint64_t now_ms = (uint64_t)(esp_timer_get_time()/1000ULL);
    ESP_LOGI(TAG, "Reconnect timer fired: attempting STA reconnect");
    esp_wifi_connect();
    s_last_sta_connect_ms = now_ms;
}

// Connectivity watchdog: record successes/failures and open captive portal if network is unreachable
static void net_fail_report(bool ok) {
    uint64_t now = millis64();
    if (ok) {
        s_net_failures = 0;
        s_net_first_fail_ms = 0;
        return;
    }
    if (s_net_first_fail_ms == 0 || (now - s_net_first_fail_ms) > NET_FAIL_WINDOW_MS) {
        s_net_first_fail_ms = now;
        s_net_failures = 0;
    }
    s_net_failures++;
    if (!s_portal_active && s_net_failures >= NET_FAIL_THRESHOLD) {
        ESP_LOGW(TAG, "Network failures=%d within %llu ms -> starting captive portal for reconfiguration", s_net_failures, (unsigned long long)(now - s_net_first_fail_ms));
        start_portal();
        s_net_failures = 0;
        s_net_first_fail_ms = 0;
    }
}

static void wifi_init_sta(void) {
    ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_STA));
    ESP_ERROR_CHECK(esp_wifi_start());
    ESP_LOGI(TAG, "WiFi STA started (stored creds if present)");
    // Kick off immediate connection attempt to stored credentials
    esp_wifi_connect();
}

// (Provisioning manager removed) using custom portal functions.

// ================ SNTP time ================

static void sntp_start(void) {
    esp_sntp_setoperatingmode(SNTP_OPMODE_POLL);
    esp_sntp_setservername(0, "time.nist.gov");
    esp_sntp_init();
}

static void wait_for_time(uint32_t timeout_ms) {
    uint64_t start = (uint64_t)(esp_timer_get_time() / 1000ULL);
    for (;;) {
        time_t now = 0;
        struct tm info = {0};
        time(&now);
        localtime_r(&now, &info);
        if (info.tm_year >= (2020 - 1900)) break; // time is valid
        if (((uint64_t)(esp_timer_get_time() / 1000ULL) - start) > timeout_ms) break;
        vTaskDelay(pdMS_TO_TICKS(200));
    }
}

static bool get_time_str(char out[20]) {
    time_t now = 0;
    struct tm info = {0};
    time(&now);
    localtime_r(&now, &info);
    if (info.tm_year < (2016 - 1900)) return false;
    // Adjust timezone manually if desired (e.g., -3 hours)
    // now -= 3 * 3600; localtime_r(&now, &info);
    strftime(out, 20, "%Y-%m-%d %H:%M:%S", &info);
    return true;
}

// ================ mDNS ================

static bool mdns_advertise(void) {
    uint8_t mac[6];
    esp_read_mac(mac, ESP_MAC_WIFI_STA);

    char suffix[7];
    sprintf(suffix, "%02X%02X%02X", mac[3], mac[4], mac[5]);

    char mac_colons[18];
    mac_to_str(mac, mac_colons, sizeof(mac_colons), true);

    char host[40];
    sprintf(host, "Flow Hall-%s", mac_colons);

    ESP_ERROR_CHECK(mdns_init());
    mdns_hostname_set(host);
    // Set instance name to Purific-XXXXXX (last 6 digits of MAC)
    mdns_instance_name_set(host);

    // Advertise HTTP on port 80
    mdns_service_add(NULL, "_http", "_tcp", 80, NULL, 0);

    // TXT records
    mdns_service_txt_item_set("_http", "_tcp", "mac", suffix);
    mdns_service_txt_item_set("_http", "_tcp", "id", mac_colons);
    mdns_service_txt_item_set("_http", "_tcp", "device", "Purific");

    ESP_LOGI(TAG, "mDNS started as %s", host);
    return true;
}

// ================ HTTP helpers ================

static esp_err_t http_post_json(const char* url, const char* json, char* resp, size_t resp_len, int* http_status) {
    if (resp && resp_len) resp[0] = 0;
    esp_http_client_config_t cfg = {
        .url = url,
        .method = HTTP_METHOD_POST,
#ifdef CONFIG_MBEDTLS_CERTIFICATE_BUNDLE
        .crt_bundle_attach = esp_crt_bundle_attach,
#else
        .cert_pem = server_root_cert_pem,
#endif
        .timeout_ms = 15000,
        .disable_auto_redirect = false,
    };
    esp_http_client_handle_t client = esp_http_client_init(&cfg);
    if (!client) return ESP_FAIL;

    esp_http_client_set_header(client, "Content-Type", "application/json");
    esp_http_client_set_header(client, "Accept", "application/json,text/plain,*/*");
    size_t len = strlen(json);
    esp_err_t err = esp_http_client_open(client, len);
    if (err != ESP_OK) {
        ESP_LOGW(TAG, "http_post_json: open failed %s", esp_err_to_name(err));
        net_fail_report(false);

        esp_http_client_cleanup(client);
        return err;
    }
    int written = esp_http_client_write(client, json, len);
    if (written < 0 || (size_t)written != len) {
        ESP_LOGW(TAG, "http_post_json: write mismatch %d/%zu", written, len);
    }
    int64_t content_len = esp_http_client_fetch_headers(client); // also returns length or -1
    if (http_status) *http_status = esp_http_client_get_status_code(client);
    ESP_LOGD(TAG, "http_post_json: status=%d content_len=%lld", http_status?*http_status:-1, (long long)content_len);

    // Read body fully (even if chunked => content_len == -1)
    if (resp && resp_len > 1) {
        int total = 0;
        while (total < (int)resp_len - 1) {
            int r = esp_http_client_read(client, resp + total, (int)resp_len - 1 - total);
            if (r <= 0) break;
            total += r;
        }
        resp[total] = 0;
        ESP_LOGD(TAG, "http_post_json: body_len=%d body='%.*s'", total, total, resp);
    }

    int status_local = http_status ? *http_status : esp_http_client_get_status_code(client);
    net_fail_report((status_local >= 200 && status_local < 300));

    esp_http_client_close(client);
    esp_http_client_cleanup(client);
    return ESP_OK;
}

static void send_ip_to_backend(void) {
    // Get MAC and IP
    uint8_t mac[6];
    esp_read_mac(mac, ESP_MAC_WIFI_STA);
    char mac_str[18];
    mac_to_str(mac, mac_str, sizeof(mac_str), true);

    esp_netif_t* netif = esp_netif_get_handle_from_ifkey("WIFI_STA_DEF");
    esp_netif_ip_info_t ip;
    char ip_str[16] = "0.0.0.0";
    if (netif && esp_netif_get_ip_info(netif, &ip) == ESP_OK) {
        sprintf(ip_str, IPSTR, IP2STR(&ip.ip));
    }

    char payload[192];
    snprintf(payload, sizeof(payload), "{\"id\":\"%s\",\"ip_address\":\"%s\"}", mac_str, ip_str);

    int status = 0;
    esp_err_t err = http_post_json(URL_DEVICE_IP, payload, NULL, 0, &status);
    ESP_LOGI(TAG, "send_ip_to_backend: http=%d err=%s", status, esp_err_to_name(err));
}

static void report_firmware_version(void) {
    uint8_t mac[6];
    esp_read_mac(mac, ESP_MAC_WIFI_STA);
    char mac_str[18];
    mac_to_str(mac, mac_str, sizeof(mac_str), true);

    const char* chip = get_chip_model();

    char payload[256];
    snprintf(payload, sizeof(payload),
             "{\"sensor_id\":\"%s\",\"firmware_version\":\"%s\",\"chip_model\":\"%s\"}",
             mac_str, FIRMWARE_VERSION, chip);

    int status = 0;
    esp_err_t err = http_post_json(URL_REPORT_FIRMWARE_VERSION, payload, NULL, 0, &status);
    ESP_LOGI(TAG, "report_firmware_version: http=%d err=%s", status, esp_err_to_name(err));
}

static void fetch_calibration_factor(void) {
    uint8_t mac[6];
    esp_read_mac(mac, ESP_MAC_WIFI_STA);
    char mac_str[18];
    mac_to_str(mac, mac_str, sizeof(mac_str), true);

    char payload[128];
    snprintf(payload, sizeof(payload), "{\"sensor_id\":\"%s\"}", mac_str);

    char resp[256];
    int status = 0;
    esp_err_t err = http_post_json(URL_GET_CALIBRATION_FACTOR, payload, resp, sizeof(resp), &status);
    ESP_LOGI(TAG, "fetch_calibration_factor: http=%d err=%s resp=%s", status, esp_err_to_name(err), resp);
    if (err == ESP_OK && status >= 200 && status < 300) {
        ESP_LOGI(TAG, "fetch_calibration_factor raw: %s", resp);
        const char* key = "\"calibration_factor\"";
        char* p = strstr(resp, key);
        if (p) {
            p = strchr(p + strlen(key), ':');
            if (p) {
                p++; // move past ':'
                while (*p == ' ' || *p == '"') p++; // skip spaces/quotes
                char num[32]; int i = 0;
                while (*p && i < (int)sizeof(num) - 1 && ((*p >= '0' && *p <= '9') || *p == '.')) {
                    num[i++] = *p++;
                }
                num[i] = 0;
                if (i > 0) {
                    double v = atof(num);
                    if (v > 0.0) {
                        s_calibration_factor = v;
                        ESP_LOGI(TAG, "Using calibration factor: %.10f", s_calibration_factor);
                    } else {
                        ESP_LOGW(TAG, "Calibration factor parsed but value not > 0 (num=%s)", num);
                    }
                } else {
                    ESP_LOGW(TAG, "Calibration factor key found but no numeric value");
                }
            }
        } else {
            ESP_LOGW(TAG, "Calibration factor key not found in response");
        }
    } else {
        ESP_LOGW(TAG, "Failed fetch calibration: http=%d err=%s", status, esp_err_to_name(err));
    }
}

static void envia_dados(double fluxo, double volume) {
    uint8_t mac[6];
    esp_read_mac(mac, ESP_MAC_WIFI_STA);
    char mac_str[18];
    mac_to_str(mac, mac_str, sizeof(mac_str), true);

    char ts[20];
    if (!get_time_str(ts)) {
        strcpy(ts, "1970-01-01 00:00:00");
    }

    char payload[160];
    snprintf(payload, sizeof(payload),
             "{\"id\":\"%s\",\"fluxo\":%.2f,\"volume\":%.2f,\"data\":\"%s\"}",
             mac_str, (float)fluxo, (float)volume, ts);

    int status = 0;
    esp_err_t err = http_post_json(URL_ADD_READING, payload, NULL, 0, &status);
    ESP_LOGI(TAG, "envia_dados: http=%d err=%s", status, esp_err_to_name(err));
}

static void envia_tds(double tds) {
    uint8_t mac[6];
    esp_read_mac(mac, ESP_MAC_WIFI_STA);
    char mac_str[18];
    mac_to_str(mac, mac_str, sizeof(mac_str), true);

    char ts[20];
    if (!get_time_str(ts)) {
        strcpy(ts, "1970-01-01 00:00:00");
    }

    char payload[128];
    snprintf(payload, sizeof(payload),
             "{\"id\":\"%s\",\"tds\":%.2f,\"data\":\"%s\"}",
             mac_str, (float)tds, ts);

    int status = 0;
    esp_err_t err = http_post_json(URL_ADD_TDS, payload, NULL, 0, &status);
    ESP_LOGI(TAG, "envia_tds: http=%d err=%s", status, esp_err_to_name(err));

    s_tds_valid = false;
}

// ================ GPIO / ISR ================

static void IRAM_ATTR hall_isr(void* arg) {
    s_pulse_count++;
}

// ================ MQTT ================

static void mqtt_publish(const char* topic, const char* payload) {
    if (s_mqtt) {
        esp_mqtt_client_publish(s_mqtt, topic, payload, 0, 1, 0);
    }
}

static void send_update_success_message_if_pending(void) {
    if (!s_update_pending.updateCompleted || strlen(s_update_pending.correlationId) == 0) return;

    // build small JSON
    char payload[320];
    snprintf(payload, sizeof(payload),
             "{\"type\":\"response\",\"correlation_id\":\"%s\",\"action\":\"update_firmware\",\"from\":\"%s\",\"status\":\"success\",\"message\":\"Atualização de firmware concluída com sucesso - confirmação pós-restart\"}",
             s_update_pending.correlationId, s_mqtt_client_id);
    int msg_id1 = esp_mqtt_client_publish(s_mqtt, s_mqtt_topic_geral, payload, 0, 1, 1);
    ESP_LOGI(TAG, "Post-restart success published (compat,retain,1/2) msg_id=%d", msg_id1);
    vTaskDelay(pdMS_TO_TICKS(600));
    int msg_id2 = esp_mqtt_client_publish(s_mqtt, s_mqtt_topic_geral, payload, 0, 1, 1);
    ESP_LOGI(TAG, "Post-restart success published (compat,retain,2/2) msg_id=%d", msg_id2);

    clear_update_status();
    s_update_pending.updateCompleted = false;
    s_update_pending.correlationId[0] = 0;
}

static void mqtt_post_restart_success_task(void* pv) {
    // Give MQTT a moment to settle after CONNECT and SUBSCRIBE
    vTaskDelay(pdMS_TO_TICKS(1500));
    if (s_update_pending.updateCompleted && strlen(s_update_pending.correlationId) > 0) {
        char payload[320];
        snprintf(payload, sizeof(payload),
                 "{\"type\":\"response\",\"correlation_id\":\"%s\",\"action\":\"update_firmware\",\"from\":\"%s\",\"status\":\"success\",\"message\":\"Atualização de firmware concluída com sucesso - confirmação pós-restart\"}",
                 s_update_pending.correlationId, s_mqtt_client_id);
        // Publish twice with QoS1 and retain to maximize delivery odds
        int msg_id1 = esp_mqtt_client_publish(s_mqtt, s_mqtt_topic_geral, payload, 0, 1, 1);
        ESP_LOGI(TAG, "Post-restart success published (retain,1/2) msg_id=%d", msg_id1);
        vTaskDelay(pdMS_TO_TICKS(1000));
        int msg_id2 = esp_mqtt_client_publish(s_mqtt, s_mqtt_topic_geral, payload, 0, 1, 1);
        ESP_LOGI(TAG, "Post-restart success published (retain,2/2) msg_id=%d", msg_id2);
        clear_update_status();
        s_update_pending.updateCompleted = false;
        s_update_pending.correlationId[0] = 0;
    }
    vTaskDelete(NULL);
}

// ================= Stepper / Valve control functions =================
static inline void step_enable_driver(void) { gpio_set_level(PIN_ENABLE_SHARED, 0); }
static inline void step_disable_driver(void) { gpio_set_level(PIN_ENABLE_SHARED, 1); }

static inline void step_wake_cold(void) { gpio_set_level(PIN_RSTSLP_COLD, 1); }
static inline void step_sleep_cold(void) { gpio_set_level(PIN_RSTSLP_COLD, 0); }
static inline void step_wake_nat(void)  { gpio_set_level(PIN_RSTSLP_NAT, 1); }
static inline void step_sleep_nat(void) { gpio_set_level(PIN_RSTSLP_NAT, 0); }

static void step_pulse_shared(int steps) {
    for (int i = 0; i < steps; ++i) {
        gpio_set_level(PIN_STEP_SHARED, 1);
        ets_delay_us(10000); // 10ms pulse width total cycle 20ms ~50Hz (conservative)
        gpio_set_level(PIN_STEP_SHARED, 0);
        ets_delay_us(10000);
    }
}

static void step_with_direction(bool dir, int steps) {
    gpio_set_level(PIN_DIR_SHARED, dir ? 1 : 0);
    step_pulse_shared(steps);
}

static void open_cold_valve(void) {
    step_wake_cold();
    step_enable_driver();
    step_with_direction(DIR_OPEN_COLD, VALVE_STEPS_OPEN);
    s_valve_cold_open = true;
}
static void close_cold_valve(void) {
    step_wake_cold();
    step_enable_driver();
    step_with_direction(DIR_CLOSE_COLD, VALVE_STEPS_CLOSE);
    s_valve_cold_open = false;
    step_sleep_cold();
}
static void open_nat_valve(void) {
    step_wake_nat();
    step_enable_driver();
    step_with_direction(DIR_OPEN_NAT, VALVE_STEPS_OPEN);
    s_valve_nat_open = true;
}
static void close_nat_valve(void) {
    step_wake_nat();
    step_enable_driver();
    step_with_direction(DIR_CLOSE_NAT, VALVE_STEPS_CLOSE);
    s_valve_nat_open = false;
    step_sleep_nat();
}

static void handle_dispensing(void) {
    if (s_dispense_state == DISPENSE_IDLE) return;
    uint64_t now_ms = millis64();
    uint64_t required = (uint64_t)(s_ms_per_ml * (double)s_dispense_volume_ml);
    if (now_ms - s_dispense_start_ms >= required) {
        if (s_dispense_state == DISPENSING_COLD) {
            close_cold_valve();
        } else if (s_dispense_state == DISPENSING_NATURAL) {
            close_nat_valve();
        }
        s_dispense_state = DISPENSE_IDLE;
        ESP_LOGI(TAG, "Dispensing complete");
    }
}

static void ota_task(void* pv) {
    char* correlation = (char*)pv;

    // Inform "in_progress" was already sent before launching this task
    // Append chip model to request the correct binary variant (prevents chip-id mismatch)
    const char* chip = get_chip_model();
    char url_with_chip[256];
    snprintf(url_with_chip, sizeof(url_with_chip), "%s%schip_model=%s",
             URL_DOWNLOAD_FIRMWARE,
             (strchr(URL_DOWNLOAD_FIRMWARE, '?') ? "&" : "?"),
             chip ? chip : "");

    esp_http_client_config_t http_cfg = {
        .url = url_with_chip,
    // Prefer bundle; fallback to embedded PEM
#ifdef CONFIG_MBEDTLS_CERTIFICATE_BUNDLE
    .crt_bundle_attach = esp_crt_bundle_attach,
#else
    .cert_pem = server_root_cert_pem,
#endif
        .timeout_ms = 15000,
        .keep_alive_enable = true,
    };
    esp_https_ota_config_t ota_cfg = {
        .http_config = &http_cfg,
        .partial_http_download = false,
        .max_http_request_size = 0,
    };

    ESP_LOGI(TAG, "Starting OTA from %s", url_with_chip);
    esp_err_t ret = esp_https_ota(&ota_cfg);
    if (ret == ESP_OK) {
        ESP_LOGI(TAG, "OTA Success, reporting version and restarting...");
        report_firmware_version();
        vTaskDelay(pdMS_TO_TICKS(5000));
        esp_restart();
    } else {
        ESP_LOGE(TAG, "OTA failed: %s", esp_err_to_name(ret));
        clear_update_status();

        char payload[256];
    snprintf(payload, sizeof(payload),
                 "{\"type\":\"response\",\"correlation_id\":\"%s\",\"action\":\"update_firmware\",\"from\":\"%s\",\"status\":\"error\",\"message\":\"Falha ao realizar a atualização de firmware\"}",
         correlation ? correlation : "", s_mqtt_client_id);
        mqtt_publish(s_mqtt_topic_geral, payload);
    }
    if (correlation) free(correlation);
    vTaskDelete(NULL);
}

static void mqtt_event_handler(void* handler_args, esp_event_base_t base, int32_t event_id, void* event_data) {
    esp_mqtt_event_handle_t e = (esp_mqtt_event_handle_t)event_data;
    switch (event_id) {
        case MQTT_EVENT_CONNECTED: {
            ESP_LOGI(TAG, "MQTT connected");
            net_fail_report(true);

            int msg_id = esp_mqtt_client_subscribe(s_mqtt, s_mqtt_topic_geral, 1);
            ESP_LOGI(TAG, "Subscribed to: %s (msg_id=%d)", s_mqtt_topic_geral, msg_id);

            char connectMsg[160];
            snprintf(connectMsg, sizeof(connectMsg),
                     "{\"type\":\"status\",\"status\":\"connected\",\"client\":\"%s\"}", s_mqtt_client_id);
            mqtt_publish(s_mqtt_topic_geral, connectMsg);

            // Send pending update success (if any) after a short delay to improve delivery reliability
            if (s_update_pending.updateCompleted && strlen(s_update_pending.correlationId) > 0) {
                xTaskCreate(mqtt_post_restart_success_task, "mqtt_post_restart_success", 3072, NULL, 5, NULL);
            }
        } break;
        case MQTT_EVENT_DISCONNECTED: {
            ESP_LOGW(TAG, "MQTT disconnected");
            net_fail_report(false);
        } break;
        case MQTT_EVENT_ERROR: {
            ESP_LOGW(TAG, "MQTT error: event_id=%d err_type=%d", (int)event_id, (int)e->error_handle ? e->error_handle->error_type : -1);
            net_fail_report(false);
        } break;
            case MQTT_EVENT_PUBLISHED: {
                ESP_LOGI(TAG, "MQTT published (msg_id=%d)", e->msg_id);
            } break;
            case MQTT_EVENT_DATA: {
            // Copy payload to null-terminated buffer
            int len = e->data_len;
            if (len <= 0 || len > 1023) break;
            char msg[1024];
            memcpy(msg, e->data, len);
            msg[len] = 0;
            ESP_LOGI(TAG, "MQTT message on %.*s: %s", e->topic_len, e->topic, msg);

            // Very small/naive JSON parsing for keys we need
            // Expect fields: type, action, correlation_id, from
            const char* action_key = "\"action\"";
            const char* from_key = "\"from\"";
            const char* corr_key = "\"correlation_id\"";
            const char* type_key = "\"type\"";

            char action[48] = {0};
            char from[96] = {0};
            char correlation[48] = {0};
            char type[24] = {0};
            char* p = NULL;
            if ((p = strstr(msg, type_key))) {
                p = strchr(p + strlen(type_key), ':');
                if (p) {
                    while (*p && (*p == ':' || *p == ' ')) p++;
                    if (*p == '\"') {
                        p++;
                        char* q = strchr(p, '\"');
                        if (q) { size_t n = (size_t)(q - p); if (n < sizeof(type)) { memcpy(type, p, n); type[n]=0; } }
                    }
                }
            }


            if ((p = strstr(msg, action_key))) {
                p = strchr(p + strlen(action_key), ':');
                if (p) {
                    while (*p && (*p == ':' || *p == ' ')) p++;
                    if (*p == '\"') {
                        p++;
                        char* q = strchr(p, '\"');
                        if (q) { size_t n = (size_t)(q - p); if (n < sizeof(action)) { memcpy(action, p, n); action[n]=0; } }
                    }
                }
            }
            if ((p = strstr(msg, from_key))) {
                p = strchr(p + strlen(from_key), ':');
                if (p) {
                    while (*p && (*p == ':' || *p == ' ')) p++;
                    if (*p == '\"') {
                        p++;
                        char* q = strchr(p, '\"');
                        if (q) { size_t n = (size_t)(q - p); if (n < sizeof(from)) { memcpy(from, p, n); from[n]=0; } }
                    }
                }
            }
            if ((p = strstr(msg, corr_key))) {
                p = strchr(p + strlen(corr_key), ':');
                if (p) {
                    while (*p && (*p == ':' || *p == ' ')) p++;
                    if (*p == '\"') {
                        p++;
                        char* q = strchr(p, '\"');
                        if (q) { size_t n = (size_t)(q - p); if (n < sizeof(correlation)) { memcpy(correlation, p, n); correlation[n]=0; } }
                    }
                }
            }

            // Ignore messages from self
            if (strlen(from) && strcmp(from, s_mqtt_client_id) == 0) break;

            // Only act on explicit commands
            if (strcmp(type, "command") != 0) break;
            if (strcmp(action, "update_firmware") == 0) {
                // Save correlation and inform in_progress
                save_update_status(correlation);

                char resp[320];
                snprintf(resp, sizeof(resp),
                         "{\"type\":\"response\",\"correlation_id\":\"%s\",\"action\":\"update_firmware\",\"from\":\"%s\",\"status\":\"in_progress\",\"message\":\"Iniciando atualização de firmware\"}",
                         correlation, s_mqtt_client_id);
                mqtt_publish(s_mqtt_topic_geral, resp);

                ESP_LOGI(TAG, "Starting OTA as requested (correlation_id=%s)", correlation);

                // Start OTA in a separate task
                xTaskCreate(ota_task, "ota_task", 8192, strdup(correlation), 5, NULL);
            } else if (strcmp(action, "toggle_cold_water") == 0) {
                if (s_valve_cold_open) {
                    close_cold_valve();
                } else {
                    open_cold_valve();
                }
                char resp[256];
                snprintf(resp, sizeof(resp),
                         "{\"type\":\"response\",\"correlation_id\":\"%s\",\"action\":\"toggle_cold_water\",\"from\":\"%s\",\"status\":\"success\"}",
                         correlation, s_mqtt_client_id);
                mqtt_publish(s_mqtt_topic_geral, resp);
            } else if (strcmp(action, "toggle_natural_water") == 0) {
                if (s_valve_nat_open) {
                    close_nat_valve();
                } else {
                    open_nat_valve();
                }
                char resp[256];
                snprintf(resp, sizeof(resp),
                         "{\"type\":\"response\",\"correlation_id\":\"%s\",\"action\":\"toggle_natural_water\",\"from\":\"%s\",\"status\":\"success\"}",
                         correlation, s_mqtt_client_id);
                mqtt_publish(s_mqtt_topic_geral, resp);
            } else if (strcmp(action, "natural_water_with_volume") == 0 || strcmp(action, "cold_water_with_volume") == 0) {
                // Extract volume integer (very simple parse for "volume":NUMBER)
                int volume_ml = 0; char* pv = strstr(msg, "\"volume\"");
                if (pv) {
                    pv = strchr(pv, ':');
                    if (pv) {
                        pv++;
                        volume_ml = atoi(pv);
                    }
                }
                if (volume_ml > 0 && s_dispense_state == DISPENSE_IDLE) {
                    s_dispense_volume_ml = volume_ml;
                    s_dispense_start_ms = (uint32_t)millis64();
                    if (strcmp(action, "natural_water_with_volume") == 0) {
                        open_nat_valve();
                        s_dispense_state = DISPENSING_NATURAL;
                    } else {
                        open_cold_valve();
                        s_dispense_state = DISPENSING_COLD;
                    }
                }
                char resp[256];
                snprintf(resp, sizeof(resp),
                         "{\"type\":\"response\",\"correlation_id\":\"%s\",\"action\":\"%s\",\"from\":\"%s\",\"status\":\"success\"}",
                         correlation, action, s_mqtt_client_id);
                mqtt_publish(s_mqtt_topic_geral, resp);
            } else {
                char resp[320];
                snprintf(resp, sizeof(resp),
                         "{\"type\":\"response\",\"correlation_id\":\"%s\",\"action\":\"%s\",\"from\":\"%s\",\"status\":\"error\",\"message\":\"Ação desconhecida\"}",
                         correlation, action, s_mqtt_client_id);
                mqtt_publish(s_mqtt_topic_geral, resp);
            }
        } break;
        default:
            break;
    }
}

static void mqtt_init_and_start(void) {
    uint8_t mac[6];
    esp_read_mac(mac, ESP_MAC_WIFI_STA);
    char mac_colons[18];
    mac_to_str(mac, mac_colons, sizeof(mac_colons), true);

    // Match Arduino implementation: use MAC with colons in client ID and topic
    snprintf(s_mqtt_client_id, sizeof(s_mqtt_client_id), "ESP32_Purificador_%s", mac_colons);
    snprintf(s_mqtt_topic_geral, sizeof(s_mqtt_topic_geral), "purificador/%s/geral", mac_colons);
    ESP_LOGI(TAG, "MQTT client_id=%s, topic=%s", s_mqtt_client_id, s_mqtt_topic_geral);

    esp_mqtt_client_config_t cfg = {
        .broker.address.uri = "mqtt://" MQTT_BROKER,
        .broker.address.port = MQTT_PORT,
        .credentials.username = MQTT_USER,
        .credentials.authentication.password = MQTT_PASSWORD,
        .credentials.client_id = s_mqtt_client_id,
    .task.priority = 5,
    .session.disable_clean_session = false,
    .network.disable_auto_reconnect = false,
    .buffer.size = 512,
    };

    s_mqtt = esp_mqtt_client_init(&cfg);
    esp_mqtt_client_register_event(s_mqtt, ESP_EVENT_ANY_ID, mqtt_event_handler, NULL);
    esp_mqtt_client_start(s_mqtt);
}

// ================ Button task (reset Wi-Fi creds) ================

static void wifi_reset_task(void* pv) {
    gpio_config_t io = {
        .pin_bit_mask = 1ULL << WIFI_RESET_GPIO,
        .mode = GPIO_MODE_INPUT,
        .pull_up_en = GPIO_PULLUP_ENABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE
    };
    gpio_config(&io);
    
    for (;;) {
        if (gpio_get_level(WIFI_RESET_GPIO) == 0) {
            // pressed
            vTaskDelay(pdMS_TO_TICKS(5000));
            if (gpio_get_level(WIFI_RESET_GPIO) == 0) {
                ESP_LOGW(TAG, "Button held, full provisioning reset (erasing NVS) ...");
                if (s_mqtt) {
                    esp_mqtt_client_stop(s_mqtt);
                    esp_mqtt_client_destroy(s_mqtt);
                    s_mqtt = NULL;
                }
                // Erase entire NVS to clear Wi-Fi + provisioning state
                nvs_flash_erase();
                vTaskDelay(pdMS_TO_TICKS(300));
                esp_restart();
            }
        }
        vTaskDelay(pdMS_TO_TICKS(100));
    }
    
}

// ================ Main loop task ================

static void main_loop_task(void* pv) {
    // Configure hall GPIO + ISR
    gpio_config_t io = {
        .pin_bit_mask = 1ULL << HALL_GPIO,
        .mode = GPIO_MODE_INPUT,
        .pull_up_en = GPIO_PULLUP_DISABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_POSEDGE
    };
    gpio_config(&io);
    gpio_install_isr_service(0);
    gpio_isr_handler_add(HALL_GPIO, hall_isr, NULL);

    // Wait Wi-Fi connected
    xEventGroupWaitBits(s_wifi_event_group, WIFI_CONNECTED_BIT, pdFALSE, pdTRUE, portMAX_DELAY);

    // mDNS
    mdns_advertise();

    // SNTP
    sntp_start();
    // Ensure time is valid before HTTPS
    wait_for_time(20000);

    // Fetch calibration factor
    fetch_calibration_factor();
    ESP_LOGI(TAG, "Using calibration factor: %.10f", s_calibration_factor);

    // Send IP + firmware version once connected and time synced (a short delay is fine)
    vTaskDelay(pdMS_TO_TICKS(3000));
    send_ip_to_backend();
    report_firmware_version();

    s_last_flow_ms = millis64();
    s_last_send_ms = millis64();
    s_last_heartbeat_ms = millis64();

    // ADC init for TDS
    adc_oneshot_unit_handle_t adc1 = NULL;
    adc_unit_t tds_unit = ADC_UNIT_1;
    adc_channel_t tds_channel = 0;
    if (adc_oneshot_io_to_channel(TDS_GPIO, &tds_unit, &tds_channel) == ESP_OK && tds_unit == ADC_UNIT_1) {
        adc_oneshot_unit_init_cfg_t init_cfg = { .unit_id = ADC_UNIT_1 };
        if (adc_oneshot_new_unit(&init_cfg, &adc1) == ESP_OK) {
            adc_oneshot_chan_cfg_t chan_cfg = {
                .bitwidth = ADC_BITWIDTH_DEFAULT,
                .atten = ADC_ATTEN_DB_12
            };
            if (adc_oneshot_config_channel(adc1, tds_channel, &chan_cfg) != ESP_OK) {
                ESP_LOGW(TAG, "ADC channel config failed for GPIO%d", (int)TDS_GPIO);
            }
        }
    } else {
        ESP_LOGW(TAG, "GPIO%u não suporta ADC1 neste alvo; TDS desabilitado", (unsigned)TDS_GPIO);
    }

    for (;;) {
        uint64_t now_ms = millis64();

        // Flow/volume calculation every 100ms
        if (now_ms - s_last_flow_ms >= FLOW_SAMPLE_MS) {
            double new_volume = (double)s_pulse_count * s_calibration_factor;
            double delta_volume = new_volume - s_volume_last;
            s_fluxo = delta_volume / ((now_ms - s_last_flow_ms) / 1000.0);

            //ESP_LOGI(TAG, "Delta volume: %.3f L, Fluxo: %.3f L/s, Volume total: %.3f L, ADC: %d, Pulses: %" PRIu64,
            //         delta_volume, s_fluxo, new_volume, adc1, s_pulse_count);

            // If there was flow in this window, sample TDS on GPIO1
            if (delta_volume > 0.0 && adc1) {
                int raw = 0;
                if (adc_oneshot_read(adc1, tds_channel, &raw) == ESP_OK) {
                    s_tds_value = 0.2699 * (double)raw + 4.2;
                    s_tds_valid = true;
                }
            }
            s_volume_last = new_volume;
            s_volume = new_volume;
            s_last_flow_ms = now_ms;
            // ESP_LOGI(TAG, "Fluxo: %.3f, Volume: %.3f, Pulses: %" PRIu64, s_fluxo, s_volume, s_pulse_count);
        }

        // Send heartbeat every 30s
        if (now_ms - s_last_heartbeat_ms >= HEARTBEAT_INTERVAL_MS) {
            uint32_t uptime = (uint32_t)(now_ms / 1000ULL);
            char heartbeat[96];
            snprintf(heartbeat, sizeof(heartbeat), "{\"type\":\"heartbeat\",\"uptime\":%" PRIu32 "}", uptime);
            mqtt_publish(s_mqtt_topic_geral, heartbeat);
            s_last_heartbeat_ms = now_ms;
        }

        // Periodic HTTP send
        if (now_ms - s_last_send_ms >= SEND_INTERVAL_MS) {
            envia_dados(s_fluxo, s_volume);
            if (s_tds_valid) {
                ESP_LOGI(TAG, "Enviando TDS: %.2f", s_tds_value);
                envia_tds(s_tds_value);
            }
            s_last_send_ms = now_ms;
        }

    // Handle dispensing lifecycle
    handle_dispensing();

        vTaskDelay(pdMS_TO_TICKS(10));
    }
}

// ================ app_main ================

void app_main(void) {
    // NVS
    ESP_ERROR_CHECK(nvs_flash_init());

    // Core network/event infra (needed before provisioning)
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    s_wifi_event_group = xEventGroupCreate();

    // Create default Wi-Fi STA
    esp_netif_create_default_wifi_sta();
    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    cfg.nvs_enable = true;
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));

    // Register Wi-Fi/IP events (MQTT start on IP)
    ESP_ERROR_CHECK(esp_event_handler_instance_register(WIFI_EVENT, ESP_EVENT_ANY_ID, &wifi_event_handler, NULL, NULL));
    ESP_ERROR_CHECK(esp_event_handler_instance_register(IP_EVENT, IP_EVENT_STA_GOT_IP, &wifi_event_handler, NULL, NULL));

    // Create AP netif for potential portal
    esp_netif_create_default_wifi_ap();
    s_update_pending = get_update_status();
    if (have_sta_creds()) {
        ESP_LOGI(TAG, "Found stored Wi-Fi credentials, starting STA");
        wifi_init_sta();
    } else {
        ESP_LOGI(TAG, "No credentials found, starting captive portal");
        start_portal();
    }

    // Initialize new stepper/valve GPIOs (safe defaults)
    gpio_config_t step_io = {0};
    step_io.mode = GPIO_MODE_OUTPUT;
    step_io.pull_up_en = GPIO_PULLUP_DISABLE;
    step_io.pull_down_en = GPIO_PULLDOWN_DISABLE;
    step_io.intr_type = GPIO_INTR_DISABLE;
    // Outputs: DIR, STEP, ENABLE, RST/SLP COLD, RST/SLP NAT
    uint64_t mask = (1ULL<<PIN_DIR_SHARED) | (1ULL<<PIN_STEP_SHARED) | (1ULL<<PIN_ENABLE_SHARED) | (1ULL<<PIN_RSTSLP_COLD) | (1ULL<<PIN_RSTSLP_NAT);
    step_io.pin_bit_mask = mask;
    gpio_config(&step_io);
    // Set defaults: driver disabled (EN high), channels asleep (RST/SLP low), step low, dir low
    gpio_set_level(PIN_ENABLE_SHARED, 1);
    gpio_set_level(PIN_RSTSLP_COLD, 0);
    gpio_set_level(PIN_RSTSLP_NAT, 0);
    gpio_set_level(PIN_STEP_SHARED, 0);
    gpio_set_level(PIN_DIR_SHARED, 0);

    ESP_LOGI(TAG, "Stepper GPIOs initialized (driver disabled, channels asleep)");

    // --- Log current logic level of GPIO0 at startup ---
    // Configure GPIO0 as input (it might already be used for boot / strapping, so keep it simple)
    gpio_config_t io0_cfg = {0};
    io0_cfg.pin_bit_mask = (1ULL << GPIO_NUM_0);
    io0_cfg.mode = GPIO_MODE_INPUT;
    io0_cfg.pull_up_en = GPIO_PULLUP_DISABLE; // adjust if board has external pull-ups/downs
    io0_cfg.pull_down_en = GPIO_PULLDOWN_DISABLE;
    io0_cfg.intr_type = GPIO_INTR_DISABLE;
    gpio_config(&io0_cfg);
    int io0_level = gpio_get_level(GPIO_NUM_0);
    ESP_LOGI(TAG, "GPIO0 initial level: %s", io0_level ? "HIGH" : "LOW");

    // Button watcher
    xTaskCreate(wifi_reset_task, "wifi_reset_task", 3072, NULL, 5, NULL);

    // Main loop task (will wait on connection bit)
    xTaskCreate(main_loop_task, "main_loop", 8192, NULL, 5, NULL);
}