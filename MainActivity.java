package com.pocketleads.pro;

import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.pm.PackageManager;
import android.content.ContentValues;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.graphics.Bitmap;
import android.graphics.Color;
import android.net.ConnectivityManager;
import android.net.NetworkInfo;
import android.net.Uri;
import android.net.wifi.WifiManager;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.os.PowerManager;
import android.provider.MediaStore;
import android.util.Base64;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowManager;
import android.webkit.CookieManager;
import android.webkit.JavascriptInterface;
import android.webkit.ValueCallback;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.Button;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;
import android.widget.Toast;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

/**
 * PocketLeads PRO — v5 Self-Patching Universal 1-ZIP + Instant GitHub SHA OTA Engine.
 * - Any raw Desktop Extension ZIP uploaded to GitHub as `PocketLeads-latest.zip` is detected
 *   automatically via GitHub's Contents API (`sha` fingerprint) or `ota-version.json`—even if
 *   the user ONLY uploads `PocketLeads-latest.zip` without touching `ota-version.json`!
 * - `serveExtensionAsset` transforms ANY raw Desktop Extension ZIP on-the-fly in Java RAM:
 *   injecting `/chrome-ota-patch.js` and the 7 In-Process background scripts into `views/index.html`,
 *   and patching `libs/account.js`, `libs/request-journal.js`, and `controllers/background.js`
 *   so raw Desktop ZIPs work on Android with zero blur and zero worker issues!
 */
public class MainActivity extends Activity {

    private static final String VIRTUAL_ORIGIN = "https://pocketleads.local";
    private static final String DASHBOARD_START_URL = VIRTUAL_ORIGIN + "/views/index.html";
    private static final String DEFAULT_GITHUB_RAW_BASE = "https://raw.githubusercontent.com/sh491333-arch/pocketleads-ota/main";
    private static final String DESKTOP_USER_AGENT =
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36";

    private FrameLayout rootLayout;
    private FrameLayout ghostWorkerContainer;
    private WebView dashboardWebView;

    private LinearLayout waOverlayContainer;
    private WebView waWebView;
    private int waTabId = -1;

    private final Handler mainHandler = new Handler(Looper.getMainLooper());
    private final ExecutorService ioPool = Executors.newCachedThreadPool();
    private final ExecutorService storageIoPool = Executors.newSingleThreadExecutor();
    private volatile String cachedStorageJson = null;
    private final AtomicInteger nextTabId = new AtomicInteger(100);
    private final Map<Integer, GhostTabEntry> ghostTabs = new ConcurrentHashMap<>();
    private final AtomicBoolean otaCheckInProgress = new AtomicBoolean(false);
    private long lastOtaCheckAtMs = 0L;
    private PowerManager.WakeLock extractionWakeLock;
    private WifiManager.WifiLock extractionWifiLock;
    private volatile boolean isExtractionActiveFlag = false;
    private final Runnable bgExtractionHeartbeat = new Runnable() {
        @Override
        public void run() {
            if (!isExtractionActiveFlag || isFinishing()) return;
            try {
                if (dashboardWebView != null) {
                    dashboardWebView.resumeTimers();
                    dashboardWebView.evaluateJavascript("window.__plBackgroundHeartbeatTick && window.__plBackgroundHeartbeatTick();", null);
                }
            } catch (Exception ignored) {}
            mainHandler.postDelayed(this, 1500L);
        }
    };
    private long lastBackPressMs = 0L;
    private boolean notifPermRequested = false;

    private ValueCallback<Uri[]> filePathCallback;
    private static final int FILE_CHOOSER_RESULT_CODE = 5102;
    private static final int CREATE_DOC_RESULT_CODE = 5105;
    private static final int GOOGLE_ACCOUNT_PICKER_RESULT_CODE = 5108;
    private volatile String pendingGoogleAccountCallbackId = null;
    private volatile byte[] lastDownloadedBytes = null;
    private volatile Uri lastDownloadedUri = null;
    private volatile String lastDownloadedMime = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet";
    private volatile String lastDownloadedName = "PocketLeads_Export.xlsx";

    private static class GhostTabEntry {
        final int id;
        volatile WebView webView;
        volatile String url;
        volatile String status;
        volatile boolean isWhatsApp;

        GhostTabEntry(int id, WebView webView, String url, boolean isWhatsApp) {
            this.id = id;
            this.webView = webView;
            this.url = url;
            this.status = "loading";
            this.isWhatsApp = isWhatsApp;
        }
    }

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);

        rootLayout = new FrameLayout(this);
        rootLayout.setBackgroundColor(Color.parseColor("#070B24"));

        ghostWorkerContainer = new FrameLayout(this);
        ghostWorkerContainer.setVisibility(View.INVISIBLE);
        rootLayout.addView(ghostWorkerContainer, new FrameLayout.LayoutParams(540, 420));

        dashboardWebView = new WebView(this);
        configureDashboardWebView(dashboardWebView);
        rootLayout.addView(dashboardWebView, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.MATCH_PARENT
        ));

        setupWhatsAppOverlay();
        setContentView(rootLayout);

        if (Build.VERSION.SDK_INT >= 33) {
            try {
                if (checkSelfPermission("android.permission.POST_NOTIFICATIONS") != PackageManager.PERMISSION_GRANTED) {
                    requestPermissions(new String[]{"android.permission.POST_NOTIFICATIONS"}, 5103);
                }
            } catch (Exception ignored) {}
        }

        storageIoPool.execute(() -> {
            try {
                if (cachedStorageJson == null) {
                    File f = getStorageFile();
                    if (f.exists()) {
                        try (FileInputStream fis = new FileInputStream(f);
                             ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
                            byte[] b = new byte[8192];
                            int r;
                            while ((r = fis.read(b)) != -1) bos.write(b, 0, r);
                            cachedStorageJson = new String(bos.toByteArray(), StandardCharsets.UTF_8);
                        }
                    } else {
                        cachedStorageJson = "{}";
                    }
                }
            } catch (Exception ignored) {}
        });
        dashboardWebView.loadUrl(DASHBOARD_START_URL);
        handleNotificationIntent(getIntent(), 700L);
        mainHandler.postDelayed(this::checkForOtaExtensionUpdate, 2500L);
    }

    @Override
    protected void onNewIntent(Intent intent) {
        super.onNewIntent(intent);
        setIntent(intent);
        handleNotificationIntent(intent, 150L);
    }

    private void handleNotificationIntent(Intent intent, long delayMs) {
        if (intent == null) return;
        if (intent.getBooleanExtra("pl_open_downloaded_file", false)) {
            intent.removeExtra("pl_open_downloaded_file");
            final String uriStr = intent.getStringExtra("pl_file_uri");
            final String mimeStr = intent.getStringExtra("pl_file_mime");
            final String nameStr = intent.getStringExtra("pl_file_name");
            mainHandler.postDelayed(() -> openSavedUriWithPermission(
                    uriStr != null && !uriStr.isEmpty() ? Uri.parse(uriStr) : null,
                    mimeStr != null ? mimeStr : "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                    nameStr != null ? nameStr : "PocketLeads_Export.xlsx"
            ), 150L);
            return;
        }
        if (!intent.getBooleanExtra("pl_notification_clicked", false)) return;
        final String notifId = intent.getStringExtra("pl_notification_id");
        final String notifTitle = intent.getStringExtra("pl_notification_title");
        final String notifMsg = intent.getStringExtra("pl_notification_message");
        intent.removeExtra("pl_notification_clicked");
        mainHandler.postDelayed(() -> {
            if (waOverlayContainer != null && waOverlayContainer.getVisibility() == View.VISIBLE) {
                waOverlayContainer.setVisibility(View.GONE);
            }
            if (dashboardWebView != null) {
                String js = "window.__onAndroidNotificationClicked && window.__onAndroidNotificationClicked("
                        + JSONObject.quote(notifId != null ? notifId : "pocketleads_scrape_status") + ", "
                        + JSONObject.quote(notifTitle != null ? notifTitle : "") + ", "
                        + JSONObject.quote(notifMsg != null ? notifMsg : "") + ");";
                dashboardWebView.evaluateJavascript(js, null);
            }
        }, delayMs);
    }

    @Override
    protected void onResume() {
        super.onResume();
        wakeAndHealDashboardWebView();
        if (System.currentTimeMillis() - lastOtaCheckAtMs > 120000L) {
            mainHandler.postDelayed(this::checkForOtaExtensionUpdate, 3500L);
        }
    }

    @Override
    public void onWindowFocusChanged(boolean hasFocus) {
        super.onWindowFocusChanged(hasFocus);
        if (hasFocus) {
            wakeAndHealDashboardWebView();
        }
    }

    private void wakeAndHealDashboardWebView() {
        try {
            if (rootLayout != null) {
                rootLayout.setBackgroundColor(Color.parseColor("#070B24"));
                rootLayout.invalidate();
            }
            if (dashboardWebView == null) {
                recreateDashboardWebViewSafely();
                return;
            }
            dashboardWebView.setBackgroundColor(Color.parseColor("#070B24"));
            dashboardWebView.setVisibility(View.VISIBLE);
            dashboardWebView.onResume();
            dashboardWebView.resumeTimers();
            dashboardWebView.requestLayout();
            dashboardWebView.invalidate();

            String currentUrl = dashboardWebView.getUrl();
            if (currentUrl == null || currentUrl.trim().isEmpty() || "about:blank".equalsIgnoreCase(currentUrl.trim())) {
                dashboardWebView.loadUrl(DASHBOARD_START_URL);
                return;
            }

            // Trigger immediate JS compositor repaint & verify DOM is alive after background resume
            dashboardWebView.evaluateJavascript(
                    "(function(){ try { if (window.__plOnAndroidResumeHeal) window.__plOnAndroidResumeHeal(); return (document && document.body && document.body.children.length > 0) ? 'ok' : 'empty'; } catch(e) { return 'err'; } })()",
                    value -> {
                        if (value == null || "null".equals(value) || value.contains("empty")) {
                            mainHandler.postDelayed(() -> {
                                try {
                                    if (dashboardWebView != null) {
                                        dashboardWebView.evaluateJavascript(
                                                "(function(){ return (document && document.body && document.body.children.length > 0) ? 'ok' : 'empty'; })()",
                                                val2 -> {
                                                    if (val2 == null || "null".equals(val2) || val2.contains("empty")) {
                                                        try { dashboardWebView.reload(); } catch (Exception ignored) {}
                                                    }
                                                }
                                        );
                                    }
                                } catch (Exception ignored) {}
                            }, 450L);
                        }
                    }
            );
        } catch (Exception ignored) {}
    }

    private void recreateDashboardWebViewSafely() {
        mainHandler.post(() -> {
            try {
                if (rootLayout == null || isFinishing()) return;
                if (dashboardWebView != null) {
                    try {
                        rootLayout.removeView(dashboardWebView);
                        dashboardWebView.destroy();
                    } catch (Exception ignored) {}
                    dashboardWebView = null;
                }
                dashboardWebView = new WebView(MainActivity.this);
                configureDashboardWebView(dashboardWebView);
                int insertIdx = (ghostWorkerContainer != null && ghostWorkerContainer.getParent() == rootLayout) ? 1 : 0;
                rootLayout.addView(dashboardWebView, insertIdx, new FrameLayout.LayoutParams(
                        ViewGroup.LayoutParams.MATCH_PARENT,
                        ViewGroup.LayoutParams.MATCH_PARENT
                ));
                dashboardWebView.loadUrl(DASHBOARD_START_URL);
            } catch (Exception ignored) {}
        });
    }

    private void pauseAndPersistExtractionOnClose() {
        try {
            cancelOngoingExtractionNotification();
            if (dashboardWebView != null) {
                dashboardWebView.evaluateJavascript(
                        "window.__plPauseAndCheckpointOnClose && window.__plPauseAndCheckpointOnClose();",
                        null
                );
            }
            for (GhostTabEntry entry : ghostTabs.values()) {
                if (entry != null && entry.webView != null && !entry.isWhatsApp) {
                    try {
                        entry.webView.stopLoading();
                        ghostWorkerContainer.removeView(entry.webView);
                        entry.webView.destroy();
                    } catch (Exception ignored) {}
                }
            }
        } catch (Exception ignored) {}
    }

    @Override
    protected void onPause() {
        super.onPause();
        if (!isFinishing() && dashboardWebView != null) {
            try {
                dashboardWebView.onResume();
                dashboardWebView.resumeTimers();
            } catch (Exception ignored) {}
        }
    }

    @Override
    protected void onStop() {
        if (isFinishing()) {
            pauseAndPersistExtractionOnClose();
        } else if (dashboardWebView != null) {
            try {
                dashboardWebView.onResume();
                dashboardWebView.resumeTimers();
            } catch (Exception ignored) {}
        }
        super.onStop();
    }

    @Override
    protected void onDestroy() {
        pauseAndPersistExtractionOnClose();
        super.onDestroy();
    }

    private File getOtaLiveDir() {
        return new File(getFilesDir(), "ota_extension_live");
    }

    private String resolveBaseOtaUrl() {
        String configuredBaseUrl = getString(R.string.ota_base_url);
        String baseUrl = (configuredBaseUrl != null && !configuredBaseUrl.isEmpty() && !configuredBaseUrl.contains("__OTA_BASE_URL__"))
                ? configuredBaseUrl
                : DEFAULT_GITHUB_RAW_BASE;
        if (!baseUrl.startsWith("https://raw.githubusercontent.com/")) {
            baseUrl = DEFAULT_GITHUB_RAW_BASE;
        }
        return baseUrl.replaceAll("/+$", "");
    }

    private boolean isSafeExternalScrapeUrl(String urlStr, boolean allowAppsScript) {
        if (urlStr == null) return false;
        String trimmed = urlStr.trim();
        if (!trimmed.startsWith("https://") && !trimmed.startsWith("http://")) return false;
        try {
            URL u = new URL(trimmed);
            String host = u.getHost() != null ? u.getHost().toLowerCase() : "";
            if (host.isEmpty() || host.equals("localhost") || host.equals("127.0.0.1") || host.equals("0.0.0.0")
                    || host.startsWith("10.") || host.startsWith("192.168.") || host.startsWith("169.254.")
                    || host.endsWith(".local") || host.endsWith(".internal")) {
                return false;
            }
            if (!allowAppsScript && (host.contains("script.google.com") || host.contains("workers.dev") || host.contains("github.com") || host.contains("githubusercontent.com"))) {
                return false;
            }
            return true;
        } catch (Exception e) {
            return false;
        }
    }

    private void checkForOtaExtensionUpdate() {
        if (!otaCheckInProgress.compareAndSet(false, true)) return;
        lastOtaCheckAtMs = System.currentTimeMillis();
        ioPool.execute(() -> {
            try {
                SharedPreferences prefs = getSharedPreferences("pocketleads_ota", Context.MODE_PRIVATE);
                String baseUrl = resolveBaseOtaUrl();

                String remoteBuildId = "";
                String remoteVersion = "";
                String zipUrl = "";

                // 1. Primary Instant Check: Query GitHub Contents API for `PocketLeads-latest.zip` SHA!
                //    This detects any newly uploaded `PocketLeads-latest.zip` in <1 second EVEN IF the user
                //    did NOT update `ota-version.json` and BEFORE GitHub Actions finishes running!
                if (baseUrl.contains("raw.githubusercontent.com/")) {
                    try {
                        String afterHost = baseUrl.substring(baseUrl.indexOf("raw.githubusercontent.com/") + "raw.githubusercontent.com/".length());
                        String[] parts = afterHost.split("/");
                        if (parts.length >= 3) {
                            String owner = parts[0];
                            String repo = parts[1];
                            String branch = parts[2];
                            String ghApiUrl = "https://api.github.com/repos/" + owner + "/" + repo
                                    + "/contents/PocketLeads-latest.zip?ref=" + branch + "&t=" + System.currentTimeMillis();
                            byte[] ghBytes = downloadUrlBytes(ghApiUrl, 10000);
                            if (ghBytes != null) {
                                JSONObject ghJson = new JSONObject(new String(ghBytes, StandardCharsets.UTF_8));
                                String sha = ghJson.optString("sha", "").trim();
                                String dlUrl = ghJson.optString("download_url", "").trim();
                                if (!sha.isEmpty()) {
                                    remoteBuildId = "sha-" + sha;
                                    zipUrl = (!dlUrl.isEmpty() ? dlUrl : (baseUrl + "/PocketLeads-latest.zip")) + "?v=" + sha;
                                }
                            }
                        }
                    } catch (Exception ignored) {}
                }

                // 2. Fallback / Supplement: Also check `ota-version.json`
                if (remoteBuildId.isEmpty()) {
                    String versionUrl = baseUrl + "/ota-version.json?t=" + System.currentTimeMillis();
                    byte[] metaBytes = downloadUrlBytes(versionUrl, 10000);
                    if (metaBytes != null) {
                        JSONObject meta = new JSONObject(new String(metaBytes, StandardCharsets.UTF_8));
                        remoteBuildId = meta.optString("buildId", meta.optString("version", "")).trim();
                        remoteVersion = meta.optString("version", "").trim();
                        String zipName = meta.optString("zipFile", "PocketLeads-latest.zip").trim();
                        zipUrl = zipName.startsWith("http") ? zipName : (baseUrl + "/" + zipName.replaceFirst("^/+", ""));
                        if (!zipUrl.contains("?")) {
                            zipUrl = zipUrl + "?v=" + Uri.encode(remoteBuildId) + "&t=" + System.currentTimeMillis();
                        }
                    }
                }

                if (remoteBuildId.isEmpty() || zipUrl.isEmpty()) return;

                String installedBuildId = prefs.getString("installed_build_id", "");
                File liveManifest = new File(getOtaLiveDir(), "manifest.json");
                if (remoteBuildId.equals(installedBuildId) && liveManifest.exists()) {
                    return; // Already on this exact ZIP!
                }

                byte[] zipBytes = downloadUrlBytes(zipUrl, 60000);
                if (zipBytes == null || zipBytes.length < 1000) return;

                if (extractAndInstallOtaZip(zipBytes)) {
                    // Read version from extracted manifest.json
                    try {
                        String mTxt = readExtensionText("manifest.json");
                        if (mTxt != null) {
                            JSONObject mObj = new JSONObject(mTxt);
                            remoteVersion = mObj.optString("version", remoteVersion);
                        }
                    } catch (Exception ignored) {}

                    final String finalVer = remoteVersion.isEmpty() ? "Latest" : remoteVersion;
                    prefs.edit()
                            .putString("installed_build_id", remoteBuildId)
                            .putString("installed_version", finalVer)
                            .apply();
                    mainHandler.post(() -> {
                        Toast.makeText(
                                MainActivity.this,
                                "PocketLeads Live Auto-Updated (v" + finalVer + ")!",
                                Toast.LENGTH_LONG
                        ).show();
                        if (dashboardWebView != null) {
                            dashboardWebView.clearCache(true);
                            dashboardWebView.loadUrl(DASHBOARD_START_URL);
                        }
                    });
                }
            } catch (Exception ignored) {
            } finally {
                otaCheckInProgress.set(false);
            }
        });
    }

    private boolean extractAndInstallOtaZip(byte[] zipBytes) {
        File stagingDir = new File(getFilesDir(), "ota_extension_staging");
        deleteRecursive(stagingDir);
        stagingDir.mkdirs();

        try {
            String stripPrefix = "";
            try (ZipInputStream zis = new ZipInputStream(new ByteArrayInputStream(zipBytes))) {
                ZipEntry entry;
                while ((entry = zis.getNextEntry()) != null) {
                    String name = entry.getName().replace("\\", "/");
                    if (!entry.isDirectory() && (name.equals("manifest.json") || name.endsWith("/manifest.json"))) {
                        int idx = name.lastIndexOf("manifest.json");
                        stripPrefix = name.substring(0, idx);
                        break;
                    }
                }
            }

            try (ZipInputStream zis = new ZipInputStream(new ByteArrayInputStream(zipBytes))) {
                ZipEntry entry;
                byte[] buffer = new byte[8192];
                while ((entry = zis.getNextEntry()) != null) {
                    String rawName = entry.getName().replace("\\", "/");
                    if (rawName.contains("..") || rawName.startsWith("__MACOSX")) continue;
                    String relName = (!stripPrefix.isEmpty() && rawName.startsWith(stripPrefix))
                            ? rawName.substring(stripPrefix.length())
                            : rawName;
                    relName = relName.replaceFirst("^/+", "");
                    if (relName.isEmpty()) continue;

                    File outFile = new File(stagingDir, relName);
                    if (!outFile.getCanonicalPath().startsWith(stagingDir.getCanonicalPath() + File.separator)) {
                        continue;
                    }
                    if (entry.isDirectory()) {
                        outFile.mkdirs();
                    } else {
                        File parent = outFile.getParentFile();
                        if (parent != null && !parent.exists()) parent.mkdirs();
                        try (FileOutputStream fos = new FileOutputStream(outFile)) {
                            int len;
                            while ((len = zis.read(buffer)) != -1) {
                                fos.write(buffer, 0, len);
                            }
                        }
                    }
                }
            }

            File checkManifest = new File(stagingDir, "manifest.json");
            if (!checkManifest.exists()) {
                deleteRecursive(stagingDir);
                return false;
            }

            File liveDir = getOtaLiveDir();
            deleteRecursive(liveDir);
            return stagingDir.renameTo(liveDir);
        } catch (Exception e) {
            deleteRecursive(stagingDir);
            return false;
        }
    }

    private void deleteRecursive(File f) {
        if (f == null || !f.exists()) return;
        if (f.isDirectory()) {
            File[] children = f.listFiles();
            if (children != null) {
                for (File c : children) deleteRecursive(c);
            }
        }
        f.delete();
    }

    private byte[] downloadUrlBytes(String urlStr, int timeoutMs) {
        HttpURLConnection conn = null;
        try {
            String currentUrl = urlStr;
            for (int i = 0; i < 5; i++) {
                URL u = new URL(currentUrl);
                conn = (HttpURLConnection) u.openConnection();
                conn.setInstanceFollowRedirects(true);
                conn.setConnectTimeout(timeoutMs);
                conn.setReadTimeout(timeoutMs);
                conn.setUseCaches(false);
                conn.setRequestProperty("Cache-Control", "no-cache, no-store, must-revalidate");
                conn.setRequestProperty("Pragma", "no-cache");
                conn.setRequestProperty("User-Agent", "PocketLeads-Android-OTA/5.0");
                if (currentUrl.contains("api.github.com")) {
                    conn.setRequestProperty("Accept", "application/vnd.github.v3+json");
                }
                int code = conn.getResponseCode();
                if (code == 301 || code == 302 || code == 303 || code == 307 || code == 308) {
                    String loc = conn.getHeaderField("Location");
                    conn.disconnect();
                    if (loc == null) return null;
                    currentUrl = new URL(u, loc).toString();
                    continue;
                }
                if (code != 200) return null;
                try (InputStream is = conn.getInputStream();
                     ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
                    byte[] buf = new byte[8192];
                    int r;
                    while ((r = is.read(buf)) != -1) bos.write(buf, 0, r);
                    return bos.toByteArray();
                }
            }
        } catch (Exception ignored) {
        } finally {
            if (conn != null) conn.disconnect();
        }
        return null;
    }

    // -------------------------------------------------------------------------
    // Dynamic Asset & OTA File Server with Automatic On-The-Fly Java RAM Patcher
    // -------------------------------------------------------------------------
    private File findFileIgnoreCase(File baseDir, String relPath) {
        if (baseDir == null || !baseDir.exists()) return null;
        File direct = new File(baseDir, relPath);
        if (direct.exists() && direct.isFile()) return direct;
        String[] parts = relPath.split("/");
        File cur = baseDir;
        for (int i = 0; i < parts.length; i++) {
            String part = parts[i];
            if (part.isEmpty()) continue;
            File exactChild = new File(cur, part);
            if (exactChild.exists()) {
                cur = exactChild;
                continue;
            }
            File[] children = cur.listFiles();
            File matched = null;
            if (children != null) {
                for (File c : children) {
                    if (c.getName().equalsIgnoreCase(part)) {
                        matched = c;
                        break;
                    }
                }
            }
            if (matched == null) return null;
            cur = matched;
        }
        return (cur.exists() && cur.isFile()) ? cur : null;
    }

    private InputStream openExtensionStream(String cleanPath) throws Exception {
        String baseName = cleanPath.contains("/") ? cleanPath.substring(cleanPath.lastIndexOf('/') + 1) : cleanPath;
        // 1. If an OTA Live Update is installed, serve extension files from ota_extension_live/ first (case-insensitive!)
        File otaFile = findFileIgnoreCase(getOtaLiveDir(), cleanPath);
        if (otaFile != null) {
            return new FileInputStream(otaFile);
        }
        // 2. Fallback to Android Core Runtime from android_core/ when a raw Desktop ZIP is uploaded without polyfill files
        if ("chrome-ota-v8-runtime.js".equalsIgnoreCase(baseName)
                || "chrome-android-polyfill.js".equalsIgnoreCase(baseName)
                || "chrome-ota-patch.js".equalsIgnoreCase(baseName)
                || "android-bg-worker.js".equalsIgnoreCase(baseName)
                || "android-ota-worker.js".equalsIgnoreCase(baseName)
                || "chrome-wa-tab-bridge.js".equalsIgnoreCase(baseName)) {
            try {
                return getAssets().open("android_core/" + baseName.toLowerCase());
            } catch (Exception ignored) {
                return getAssets().open("android_core/chrome-ota-patch.js");
            }
        }
        // 3. Fallback to inbuilt APK assets/pocketleads/ (with case-insensitive fallback for FoxCommon.js etc.)
        try {
            return getAssets().open("pocketleads/" + cleanPath);
        } catch (Exception e) {
            int slash = cleanPath.lastIndexOf('/');
            String dir = slash >= 0 ? ("pocketleads/" + cleanPath.substring(0, slash)) : "pocketleads";
            String targetName = slash >= 0 ? cleanPath.substring(slash + 1) : cleanPath;
            String[] list = getAssets().list(dir);
            if (list != null) {
                for (String item : list) {
                    if (item.equalsIgnoreCase(targetName)) {
                        return getAssets().open(dir + "/" + item);
                    }
                }
            }
            throw e;
        }
    }

    private String readExtensionText(String cleanPath) {
        try (InputStream is = openExtensionStream(cleanPath);
             ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
            byte[] buf = new byte[8192];
            int r;
            while ((r = is.read(buf)) != -1) bos.write(buf, 0, r);
            return new String(bos.toByteArray(), StandardCharsets.UTF_8);
        } catch (Exception e) {
            return null;
        }
    }

    private WebResourceResponse serveExtensionAsset(String rawPath) {
        String cleanPath = (rawPath == null || rawPath.isEmpty() || "/".equals(rawPath))
                ? "views/index.html"
                : rawPath.replaceFirst("^/+", "");
        try {
            String mime = guessMimeType(cleanPath);
            Map<String, String> headers = new HashMap<>();
            headers.put("Access-Control-Allow-Origin", "*");
            headers.put("Cache-Control", "no-store, no-cache, must-revalidate");

            String lowerPath = cleanPath.toLowerCase();

            // A) On-The-Fly HTML Auto-Patcher & Partial Healer for ANY Old or New Extension ZIP!
            if (lowerPath.endsWith(".html")) {
                String html = readExtensionText(cleanPath);
                if (html != null) {
                    // Fix older extension ZIPs that reference capitalised /libs/FoxCommon.js
                    html = html.replace("/libs/FoxCommon.js", "/libs/foxCommon.js")
                               .replace("libs/FoxCommon.js", "libs/foxCommon.js");

                    if (html.contains("<head>")) {
                        // Full HTML document (e.g. views/index.html, popup/license.html)
                        StringBuilder headInject = new StringBuilder("<head>");
                        if (!html.contains("name=\"viewport\"")) {
                            headInject.append("\n<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0, maximum-scale=1.0, user-scalable=no\">");
                        }
                        if (!html.contains("/chrome-ota-patch.js")) {
                            headInject.append("\n<script src=\"/chrome-ota-patch.js\"></script>");
                        }
                        html = html.replaceFirst("<head>", headInject.toString());
                    } else {
                        // AngularJS ng-include HTML partial (e.g. views/navbar.html, views/login.html)!
                        // CRITICAL: If an old GitHub Actions workflow prepended <meta viewport> or <script chrome-android-polyfill.js>
                        // to this partial, strip them out in RAM so AngularJS ng-include NEVER crashes with [$compile:tplrt]!
                        html = html.replaceAll("(?is)<meta[^>]*viewport[^>]*>\\s*", "");
                        html = html.replaceAll("(?is)<script[^>]*chrome-(?:android-polyfill|ota-patch)\\.js[^>]*>\\s*</script>\\s*", "");
                    }

                    // If serving views/index.html from a raw Desktop ZIP that doesn't have the In-Process background
                    // scripts yet, inject them right before controllers/index.js in RAM!
                    if ("views/index.html".equalsIgnoreCase(cleanPath) && !html.contains("/controllers/TaskManagerContainer.js")) {
                        StringBuilder inProcessTags = new StringBuilder();
                        String[] requiredBgScripts = new String[]{
                                "/libs/result-query.js",
                                "/libs/request-journal.js",
                                "/libs/ghost-parser.js",
                                "/libs/profile-tab.js",
                                "/libs/TaskManager.js",
                                "/controllers/TaskManagerContainer.js",
                                "/controllers/background.js"
                        };
                        for (String s : requiredBgScripts) {
                            if (readExtensionText(s.substring(1)) != null && !html.contains("src=\"" + s + "\"")) {
                                inProcessTags.append("    <script defer src=\"").append(s).append("\"></script>\n");
                            }
                        }
                        int idxPos = html.indexOf("/controllers/index.js");
                        if (idxPos > 0) {
                            int scriptStart = html.lastIndexOf("<script", idxPos);
                            if (scriptStart >= 0) {
                                html = html.substring(0, scriptStart) + inProcessTags.toString() + html.substring(scriptStart);
                            }
                        } else if (html.contains("</body>")) {
                            html = html.replaceFirst("</body>", inProcessTags.toString() + "\n</body>");
                        }
                    }

                    InputStream injectedStream = new ByteArrayInputStream(html.getBytes(StandardCharsets.UTF_8));
                    return new WebResourceResponse(mime, "UTF-8", 200, "OK", headers, injectedStream);
                }
            }

            // B) On-The-Fly JS Auto-Patcher for ANY raw Desktop Extension ZIP!
            if ("libs/account.js".equalsIgnoreCase(cleanPath)
                    || "libs/request-journal.js".equalsIgnoreCase(cleanPath)
                    || "controllers/background.js".equalsIgnoreCase(cleanPath)
                    || "profile-helpdesk.js".equalsIgnoreCase(cleanPath)) {
                String js = readExtensionText(cleanPath);
                if (js != null) {
                    if ("libs/account.js".equalsIgnoreCase(cleanPath)) {
                        js = js.replaceFirst("const\\s+worker\\s*=\\s*[^;]+;", "const worker = true;");
                    } else if ("libs/request-journal.js".equalsIgnoreCase(cleanPath)) {
                        js = js.replace(
                                "return {get:k=>transact('readonly',s=>s.get(k)),put:v=>transact('readwrite',s=>s.put(v))};",
                                "const mem=new Map();return {get:k=>transact('readonly',s=>s.get(k)).catch(()=>mem.get(k)),put:v=>transact('readwrite',s=>s.put(v)).catch(()=>{if(v&&v.slot)mem.set(v.slot,v);})};"
                        );
                    } else if ("profile-helpdesk.js".equalsIgnoreCase(cleanPath)) {
                        js = js.replace("const lic = await readLicense();", "var lic = await readLicense();");
                    } else if ("controllers/background.js".equalsIgnoreCase(cleanPath)) {
                        js = js.replace(
                                "Math.min(6000,Number(payload&&payload.timeoutMs)||5500)",
                                "Math.min(20000,Number(payload&&payload.timeoutMs)||15000)"
                        ).replace(
                                "const GHOST_TAB_MAX_URLS = 50;",
                                "const GHOST_TAB_MAX_URLS = 8;"
                        ).replace(
                                "document.body.innerText",
                                "document.body.textContent"
                        ).replace(
                                "await sleep(60);",
                                "await sleep(220);"
                        );
                    }
                    InputStream patchedJsStream = new ByteArrayInputStream(js.getBytes(StandardCharsets.UTF_8));
                    return new WebResourceResponse(mime, "UTF-8", 200, "OK", headers, patchedJsStream);
                }
            }

            InputStream is = openExtensionStream(cleanPath);
            return new WebResourceResponse(mime, "UTF-8", 200, "OK", headers, is);
        } catch (Exception e) {
            return new WebResourceResponse(
                    "text/plain",
                    "UTF-8",
                    404,
                    "Not Found",
                    null,
                    new ByteArrayInputStream("Not Found".getBytes(StandardCharsets.UTF_8))
            );
        }
    }

    @SuppressLint({"SetJavaScriptEnabled", "AddJavascriptInterface"})
    private void configureDashboardWebView(WebView webView) {
        WebSettings settings = webView.getSettings();
        settings.setJavaScriptEnabled(true);
        settings.setTextZoom(100);
        settings.setDomStorageEnabled(true);
        settings.setDatabaseEnabled(true);
        settings.setAllowFileAccess(false);
        settings.setAllowContentAccess(false);
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.JELLY_BEAN) {
            settings.setAllowFileAccessFromFileURLs(false);
            settings.setAllowUniversalAccessFromFileURLs(false);
        }
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.KITKAT) {
            WebView.setWebContentsDebuggingEnabled(false);
        }
        settings.setMediaPlaybackRequiresUserGesture(false);
        settings.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW);
        settings.setCacheMode(WebSettings.LOAD_DEFAULT);
        settings.setUseWideViewPort(true);
        settings.setLoadWithOverviewMode(true);
        settings.setSupportZoom(true);
        settings.setBuiltInZoomControls(true);
        settings.setDisplayZoomControls(false);
        webView.setBackgroundColor(Color.parseColor("#070B24"));
        webView.setLayerType(View.LAYER_TYPE_HARDWARE, null);
        webView.setOverScrollMode(View.OVER_SCROLL_NEVER);
        webView.setVerticalScrollBarEnabled(false);
        webView.setHorizontalScrollBarEnabled(false);

        CookieManager cookieManager = CookieManager.getInstance();
        cookieManager.setAcceptCookie(true);
        cookieManager.setAcceptThirdPartyCookies(webView, true);

        webView.addJavascriptInterface(new AndroidChromeBridge(), "AndroidChromeBridge");

        webView.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView view, WebResourceRequest request) {
                Uri uri = request.getUrl();
                if (uri != null && "pocketleads.local".equalsIgnoreCase(uri.getHost())) {
                    return serveExtensionAsset(uri.getPath());
                }
                return super.shouldInterceptRequest(view, request);
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
                Uri uri = request.getUrl();
                if (uri == null) return false;
                String scheme = uri.getScheme() != null ? uri.getScheme().toLowerCase() : "";
                if ("mailto".equals(scheme) || "tel".equals(scheme)) {
                    try {
                        startActivity(new Intent(Intent.ACTION_VIEW, uri));
                    } catch (Exception ignored) {}
                    return true;
                }
                if ("pocketleads.local".equalsIgnoreCase(uri.getHost())) {
                    return false;
                }
                try {
                    startActivity(new Intent(Intent.ACTION_VIEW, uri));
                } catch (Exception ignored) {}
                return true;
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                super.onPageFinished(view, url);
                try {
                    view.setBackgroundColor(Color.parseColor("#070B24"));
                    view.setVisibility(View.VISIBLE);
                    view.requestLayout();
                    view.invalidate();
                } catch (Exception ignored) {}
            }

            @Override
            public boolean onRenderProcessGone(WebView view, android.webkit.RenderProcessGoneDetail detail) {
                recreateDashboardWebViewSafely();
                return true;
            }
        });

        webView.setWebChromeClient(new WebChromeClient() {
            @Override
            public boolean onJsAlert(WebView view, String url, String message, final android.webkit.JsResult result) {
                try {
                    new android.app.AlertDialog.Builder(MainActivity.this)
                            .setTitle("PocketLeads PRO")
                            .setMessage(message)
                            .setPositiveButton("OK", (d, w) -> result.confirm())
                            .setOnCancelListener(d -> result.cancel())
                            .show();
                    return true;
                } catch (Exception e) {
                    result.confirm();
                    return true;
                }
            }

            @Override
            public boolean onJsConfirm(WebView view, String url, String message, final android.webkit.JsResult result) {
                try {
                    new android.app.AlertDialog.Builder(MainActivity.this)
                            .setTitle("PocketLeads PRO")
                            .setMessage(message)
                            .setPositiveButton("OK", (d, w) -> result.confirm())
                            .setNegativeButton("Cancel", (d, w) -> result.cancel())
                            .setOnCancelListener(d -> result.cancel())
                            .show();
                    return true;
                } catch (Exception e) {
                    result.confirm();
                    return true;
                }
            }

            @Override
            public boolean onShowFileChooser(WebView webView, ValueCallback<Uri[]> filePathCallback, FileChooserParams fileChooserParams) {
                if (MainActivity.this.filePathCallback != null) {
                    MainActivity.this.filePathCallback.onReceiveValue(null);
                }
                MainActivity.this.filePathCallback = filePathCallback;
                try {
                    Intent intent = fileChooserParams.createIntent();
                    startActivityForResult(intent, FILE_CHOOSER_RESULT_CODE);
                } catch (Exception e) {
                    MainActivity.this.filePathCallback = null;
                    return false;
                }
                return true;
            }
        });
    }

    @SuppressLint({"SetJavaScriptEnabled", "AddJavascriptInterface"})
    private void setupWhatsAppOverlay() {
        waOverlayContainer = new LinearLayout(this);
        waOverlayContainer.setOrientation(LinearLayout.VERTICAL);
        waOverlayContainer.setBackgroundColor(Color.parseColor("#0F172A"));
        waOverlayContainer.setVisibility(View.GONE);

        LinearLayout topBar = new LinearLayout(this);
        topBar.setOrientation(LinearLayout.HORIZONTAL);
        topBar.setGravity(Gravity.CENTER_VERTICAL);
        topBar.setBackgroundColor(Color.parseColor("#070B24"));
        int pad = dpToPx(10);
        topBar.setPadding(pad, pad, pad, pad);

        Button backBtn = new Button(this);
        backBtn.setText("← Back to Dashboard");
        backBtn.setTextColor(Color.WHITE);
        backBtn.setBackgroundColor(Color.parseColor("#0072FF"));
        backBtn.setOnClickListener(v -> waOverlayContainer.setVisibility(View.GONE));

        TextView titleView = new TextView(this);
        titleView.setText("  WhatsApp Web Session (Keep logged in for WA Checker)");
        titleView.setTextColor(Color.parseColor("#E2E8F0"));
        titleView.setTextSize(13f);

        topBar.addView(backBtn, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
        ));
        topBar.addView(titleView, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
        ));

        waWebView = new WebView(this);
        WebSettings ws = waWebView.getSettings();
        ws.setJavaScriptEnabled(true);
        ws.setDomStorageEnabled(true);
        ws.setDatabaseEnabled(true);
        ws.setUserAgentString(DESKTOP_USER_AGENT);
        ws.setUseWideViewPort(true);
        ws.setLoadWithOverviewMode(true);

        CookieManager.getInstance().setAcceptThirdPartyCookies(waWebView, true);
        waWebView.addJavascriptInterface(new AndroidWaTabBridge(), "AndroidWaTabBridge");

        waWebView.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView view, WebResourceRequest request) {
                Uri uri = request.getUrl();
                if (uri != null && "pocketleads.local".equalsIgnoreCase(uri.getHost())) {
                    return serveExtensionAsset(uri.getPath());
                }
                return super.shouldInterceptRequest(view, request);
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                super.onPageFinished(view, url);
                GhostTabEntry entry = ghostTabs.get(waTabId);
                if (entry != null) {
                    entry.url = url;
                    entry.status = "complete";
                }
                injectExtensionScript(waWebView, "chrome-wa-tab-bridge.js");
                injectExtensionScript(waWebView, "whatsapp/wa_preload.js");
                injectExtensionScript(waWebView, "whatsapp/wa.js");
                injectExtensionScript(waWebView, "whatsapp/pageBridge.js");
                injectExtensionScript(waWebView, "whatsapp/inject.js");
            }

            @Override
            public boolean onRenderProcessGone(WebView view, android.webkit.RenderProcessGoneDetail detail) {
                try {
                    if (waOverlayContainer != null) waOverlayContainer.setVisibility(View.GONE);
                } catch (Exception ignored) {}
                return true;
            }
        });

        waOverlayContainer.addView(topBar, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.WRAP_CONTENT
        ));
        waOverlayContainer.addView(waWebView, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                0,
                1f
        ));

        rootLayout.addView(waOverlayContainer, new FrameLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT,
                ViewGroup.LayoutParams.MATCH_PARENT
        ));
    }

    @SuppressLint("SetJavaScriptEnabled")
    private WebView createGhostWorkerWebView(final int tabId) {
        WebView wv = new WebView(this);
        WebSettings ws = wv.getSettings();
        ws.setJavaScriptEnabled(true);
        ws.setDomStorageEnabled(true);
        ws.setDatabaseEnabled(true);
        ws.setUserAgentString(DESKTOP_USER_AGENT);
        ws.setBlockNetworkImage(true);
        ws.setCacheMode(WebSettings.LOAD_NO_CACHE);
        ws.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW);
        wv.setLayerType(View.LAYER_TYPE_NONE, null);

        CookieManager.getInstance().setAcceptThirdPartyCookies(wv, true);

        wv.setWebViewClient(new WebViewClient() {
            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
                Uri uri = request.getUrl();
                if (uri == null) return false;
                String scheme = uri.getScheme() != null ? uri.getScheme().toLowerCase() : "";
                if (!"http".equals(scheme) && !"https".equals(scheme)) {
                    return true;
                }
                return false;
            }

            @Override
            public void onPageStarted(WebView view, String url, Bitmap favicon) {
                super.onPageStarted(view, url, favicon);
                GhostTabEntry entry = ghostTabs.get(tabId);
                if (entry != null) {
                    entry.url = url;
                    entry.status = "loading";
                }
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                super.onPageFinished(view, url);
                GhostTabEntry entry = ghostTabs.get(tabId);
                if (entry != null) {
                    entry.url = url;
                    entry.status = "complete";
                }
                injectExtensionScript(view, "libs/ghost-parser.js");
            }

            @Override
            public boolean onRenderProcessGone(WebView view, android.webkit.RenderProcessGoneDetail detail) {
                try {
                    ghostTabs.remove(tabId);
                    if (ghostWorkerContainer != null && view != null) {
                        ghostWorkerContainer.removeView(view);
                        view.destroy();
                    }
                } catch (Exception ignored) {}
                return true;
            }
        });

        ghostWorkerContainer.addView(wv, new FrameLayout.LayoutParams(540, 420));
        return wv;
    }

    private void injectExtensionScript(WebView targetView, String relPath) {
        String code = readExtensionText(relPath);
        if (code != null && !code.isEmpty()) {
            targetView.evaluateJavascript(code, null);
        }
    }

    private String guessMimeType(String path) {
        String lower = path.toLowerCase();
        if (lower.endsWith(".html")) return "text/html";
        if (lower.endsWith(".js")) return "application/javascript";
        if (lower.endsWith(".css")) return "text/css";
        if (lower.endsWith(".json")) return "application/json";
        if (lower.endsWith(".png")) return "image/png";
        if (lower.endsWith(".jpg") || lower.endsWith(".jpeg")) return "image/jpeg";
        if (lower.endsWith(".gif")) return "image/gif";
        if (lower.endsWith(".svg")) return "image/svg+xml";
        if (lower.endsWith(".woff2")) return "font/woff2";
        if (lower.endsWith(".woff")) return "font/woff";
        if (lower.endsWith(".ttf")) return "font/ttf";
        return "application/octet-stream";
    }

    private File getStorageFile() {
        return new File(getFilesDir(), "pocketleads_chrome_storage.json");
    }

    private void invokeDashboardCallback(final String cbId, final String payloadJson) {
        mainHandler.post(() -> {
            String safeJson = payloadJson == null ? "null" : JSONObject.quote(payloadJson);
            String js = "window.__onAndroidBridgeCallback && window.__onAndroidBridgeCallback("
                    + JSONObject.quote(cbId) + ", " + safeJson + ");";
            dashboardWebView.evaluateJavascript(js, null);
        });
    }

    public class AndroidWaTabBridge {
        @JavascriptInterface
        public void onTabMessageResponse(String cbId, String responseJson) {
            invokeDashboardCallback(cbId, responseJson);
        }
    }

    public class AndroidChromeBridge {

        @JavascriptInterface
        public void setViewportMode(final String mode) {
            mainHandler.post(() -> {
                try {
                    if (dashboardWebView != null) {
                        WebSettings s = dashboardWebView.getSettings();
                        s.setUseWideViewPort(true);
                        s.setLoadWithOverviewMode("desktop".equalsIgnoreCase(mode));
                    }
                } catch (Exception ignored) {}
            });
        }

        @JavascriptInterface
        public void triggerOtaCheckNow() {
            lastOtaCheckAtMs = 0L;
            checkForOtaExtensionUpdate();
        }

        @JavascriptInterface
        public void clearBrowsingCache() {
            mainHandler.post(() -> {
                try {
                    if (dashboardWebView != null) {
                        dashboardWebView.clearCache(true);
                        dashboardWebView.clearFormData();
                    }
                    java.util.List<Integer> toRemove = new java.util.ArrayList<>();
                    for (GhostTabEntry entry : ghostTabs.values()) {
                        if (entry != null && !entry.isWhatsApp) {
                            toRemove.add(entry.id);
                            if (entry.webView != null) {
                                try {
                                    entry.webView.stopLoading();
                                    entry.webView.clearHistory();
                                    entry.webView.clearCache(true);
                                    ghostWorkerContainer.removeView(entry.webView);
                                    entry.webView.destroy();
                                } catch (Exception ignored) {}
                            }
                        }
                    }
                    for (Integer id : toRemove) {
                        ghostTabs.remove(id);
                    }
                } catch (Exception ignored) {}
            });
            ioPool.execute(() -> {
                try {
                    deleteCacheFilesSafe(getCacheDir());
                    if (android.os.Build.VERSION.SDK_INT >= android.os.Build.VERSION_CODES.LOLLIPOP) {
                        deleteCacheFilesSafe(getCodeCacheDir());
                    }
                } catch (Exception ignored) {}
            });
        }

        private void deleteCacheFilesSafe(File dir) {
            if (dir == null || !dir.exists()) return;
            File[] children = dir.listFiles();
            if (children == null) return;
            for (File c : children) {
                if (c.isDirectory()) {
                    deleteCacheFilesSafe(c);
                }
                try { c.delete(); } catch (Exception ignored) {}
            }
        }

        @JavascriptInterface
        public String getManifestJson() {
            String m = readExtensionText("manifest.json");
            return m != null ? m : "{}";
        }

        @JavascriptInterface
        public synchronized String getAllStorageJson() {
            if (cachedStorageJson != null) return cachedStorageJson;
            File f = getStorageFile();
            if (!f.exists()) {
                cachedStorageJson = "{}";
                return "{}";
            }
            try (FileInputStream fis = new FileInputStream(f);
                 ByteArrayOutputStream bos = new ByteArrayOutputStream()) {
                byte[] buf = new byte[8192];
                int r;
                while ((r = fis.read(buf)) != -1) bos.write(buf, 0, r);
                cachedStorageJson = new String(bos.toByteArray(), StandardCharsets.UTF_8);
                return cachedStorageJson;
            } catch (Exception e) {
                return "{}";
            }
        }

        @JavascriptInterface
        public void saveAllStorageJson(final String json) {
            if (json == null) return;
            cachedStorageJson = json;
            storageIoPool.execute(() -> {
                File f = getStorageFile();
                try (FileOutputStream fos = new FileOutputStream(f, false)) {
                    fos.write(json.getBytes(StandardCharsets.UTF_8));
                    fos.flush();
                } catch (Exception ignored) {}
            });
        }

        @JavascriptInterface
        public String createTab(final String url, final boolean active) {
            final boolean isWa = url != null && url.toLowerCase().contains("whatsapp.com");
            final int tabId = isWa && waTabId > 0 ? waTabId : nextTabId.incrementAndGet();
            if (isWa) waTabId = tabId;

            final GhostTabEntry entry = new GhostTabEntry(tabId, isWa ? waWebView : null, url, isWa);
            ghostTabs.put(tabId, entry);

            mainHandler.post(() -> {
                if (isWa) {
                    entry.webView = waWebView;
                    waOverlayContainer.setVisibility(View.VISIBLE);
                    waWebView.loadUrl(url);
                } else {
                    WebView wv = createGhostWorkerWebView(tabId);
                    entry.webView = wv;
                    wv.loadUrl(url);
                }
            });

            try {
                JSONObject obj = new JSONObject();
                obj.put("id", tabId);
                obj.put("url", url);
                obj.put("active", false);
                obj.put("status", "loading");
                return obj.toString();
            } catch (Exception e) {
                return "{\"id\":" + tabId + ",\"active\":false}";
            }
        }

        @JavascriptInterface
        public String getTab(int tabId) {
            GhostTabEntry entry = ghostTabs.get(tabId);
            if (entry == null) return "null";
            try {
                JSONObject obj = new JSONObject();
                obj.put("id", entry.id);
                obj.put("url", entry.url != null ? entry.url : "");
                obj.put("active", false);
                obj.put("status", entry.status != null ? entry.status : "complete");
                return obj.toString();
            } catch (Exception e) {
                return "null";
            }
        }

        @JavascriptInterface
        public String updateTab(final int tabId, final String updatePropsJson) {
            final GhostTabEntry entry = ghostTabs.get(tabId);
            if (entry == null) return "null";
            try {
                JSONObject props = new JSONObject(updatePropsJson);
                final String newUrl = props.optString("url", "");
                if (!newUrl.isEmpty()) {
                    entry.url = newUrl;
                    entry.status = "loading";
                    mainHandler.post(() -> {
                        if (entry.webView != null) entry.webView.loadUrl(newUrl);
                    });
                }
                return getTab(tabId);
            } catch (Exception e) {
                return getTab(tabId);
            }
        }

        @JavascriptInterface
        public void removeTab(final int tabId) {
            final GhostTabEntry entry = ghostTabs.remove(tabId);
            if (entry == null) return;
            mainHandler.post(() -> {
                if (entry.isWhatsApp) {
                    waOverlayContainer.setVisibility(View.GONE);
                } else if (entry.webView != null) {
                    try {
                        ghostWorkerContainer.removeView(entry.webView);
                        entry.webView.stopLoading();
                        entry.webView.loadUrl("about:blank");
                        entry.webView.destroy();
                    } catch (Exception ignored) {}
                }
            });
        }

        @JavascriptInterface
        public void reloadTab(final int tabId) {
            final GhostTabEntry entry = ghostTabs.get(tabId);
            if (entry == null) return;
            mainHandler.post(() -> {
                if (entry.webView != null) entry.webView.reload();
            });
        }

        @JavascriptInterface
        public String queryTabs(String queryInfoJson) {
            JSONArray arr = new JSONArray();
            try {
                for (GhostTabEntry entry : ghostTabs.values()) {
                    JSONObject obj = new JSONObject();
                    obj.put("id", entry.id);
                    obj.put("url", entry.url != null ? entry.url : "");
                    obj.put("active", false);
                    obj.put("status", entry.status);
                    arr.put(obj);
                }
            } catch (Exception ignored) {}
            return arr.toString();
        }

        @JavascriptInterface
        public void executeScriptInTab(final int tabId, final String funcSource, final String argsJson, final String filesJson, final String cbId) {
            final GhostTabEntry entry = ghostTabs.get(tabId);
            if (entry == null) {
                invokeDashboardCallback(cbId, "null");
                return;
            }
            mainHandler.post(() -> {
                try {
                    if (entry.webView == null) {
                        invokeDashboardCallback(cbId, "null");
                        return;
                    }
                    if (filesJson != null && !filesJson.isEmpty()) {
                        JSONArray files = new JSONArray(filesJson);
                        for (int i = 0; i < files.length(); i++) {
                            String f = files.optString(i, "");
                            if (!f.isEmpty()) {
                                injectExtensionScript(entry.webView, f.replaceFirst("^/+", ""));
                            }
                        }
                    }
                    if (funcSource == null || funcSource.trim().isEmpty()) {
                        invokeDashboardCallback(cbId, "null");
                        return;
                    }
                    String iife = "(function(){ try { var __fn = (" + funcSource + "); var __res = __fn.apply(window, "
                            + (argsJson != null && !argsJson.isEmpty() ? argsJson : "[]")
                            + "); return (__res === undefined) ? null : __res; } catch(e) { return null; } })()";
                    entry.webView.evaluateJavascript(iife, value -> invokeDashboardCallback(cbId, value));
                } catch (Exception e) {
                    invokeDashboardCallback(cbId, "null");
                }
            });
        }

        @JavascriptInterface
        public void sendMessageToTab(final int tabId, final String messageJson, final String cbId) {
            final GhostTabEntry entry = ghostTabs.get(tabId);
            if (entry == null) {
                invokeDashboardCallback(cbId, "null");
                return;
            }
            mainHandler.post(() -> {
                if (entry.webView == null) {
                    invokeDashboardCallback(cbId, "null");
                    return;
                }
                String js = "window.__plDispatchTabMessage && window.__plDispatchTabMessage("
                        + messageJson + ", " + JSONObject.quote(cbId) + ");";
                entry.webView.evaluateJavascript(js, null);
            });
        }

        @JavascriptInterface
        public void nativeFetchAsync(final String urlStr, final String method, final String headersJson, final String body, final int timeoutMs, final String cbId) {
            ioPool.execute(() -> {
                JSONObject res = new JSONObject();
                HttpURLConnection conn = null;
                try {
                    if (!isSafeExternalScrapeUrl(urlStr, true)) {
                        res.put("ok", false);
                        res.put("status", 0);
                        res.put("error", "Blocked unsafe URL scheme or host");
                        invokeDashboardCallback(cbId, res.toString());
                        return;
                    }
                    String currentUrl = urlStr;
                    String currentMethod = method != null ? method.toUpperCase() : "GET";
                    String currentBody = body;

                    for (int redirects = 0; redirects < 6; redirects++) {
                        URL u = new URL(currentUrl);
                        conn = (HttpURLConnection) u.openConnection();
                        conn.setInstanceFollowRedirects(false);
                        conn.setConnectTimeout(Math.max(5000, timeoutMs));
                        conn.setReadTimeout(Math.max(5000, timeoutMs));
                        conn.setRequestMethod(currentMethod);
                        conn.setRequestProperty("User-Agent", DESKTOP_USER_AGENT);

                        if (headersJson != null && !headersJson.isEmpty()) {
                            JSONObject hObj = new JSONObject(headersJson);
                            Iterator<String> keys = hObj.keys();
                            while (keys.hasNext()) {
                                String k = keys.next();
                                conn.setRequestProperty(k, hObj.optString(k, ""));
                            }
                        }

                        if ("POST".equals(currentMethod) && currentBody != null) {
                            conn.setDoOutput(true);
                            byte[] outBytes = currentBody.getBytes(StandardCharsets.UTF_8);
                            try (OutputStream os = conn.getOutputStream()) {
                                os.write(outBytes);
                            }
                        }

                        int code = conn.getResponseCode();
                        if (code == 301 || code == 302 || code == 303 || code == 307 || code == 308) {
                            String loc = conn.getHeaderField("Location");
                            conn.disconnect();
                            if (loc == null || loc.isEmpty()) break;
                            currentUrl = new URL(u, loc).toString();
                            if (code == 301 || code == 302 || code == 303) {
                                currentMethod = "GET";
                                currentBody = null;
                            }
                            continue;
                        }

                        String contentType = conn.getContentType();
                        if (contentType != null) {
                            String ctLower = contentType.toLowerCase();
                            if (ctLower.startsWith("image/") || ctLower.startsWith("video/") || ctLower.startsWith("audio/")
                                    || ctLower.contains("application/pdf") || ctLower.contains("application/zip")
                                    || ctLower.contains("application/octet-stream")) {
                                res.put("ok", false);
                                res.put("status", code);
                                res.put("error", "Binary content skipped");
                                break;
                            }
                        }
                        InputStream is = (code >= 200 && code < 400) ? conn.getInputStream() : conn.getErrorStream();
                        String responseText = "";
                        if (is != null) {
                            ByteArrayOutputStream bos = new ByteArrayOutputStream();
                            byte[] buf = new byte[8192];
                            int r;
                            int total = 0;
                            int maxBytes = (currentUrl != null && (currentUrl.contains("script.google.com") || currentUrl.contains("workers.dev") || currentUrl.contains("google.com/maps") || currentUrl.contains("google.com/search"))) ? 2500000 : 250000;
                            while ((r = is.read(buf)) != -1 && total < maxBytes) {
                                bos.write(buf, 0, r);
                                total += r;
                            }
                            is.close();
                            responseText = new String(bos.toByteArray(), StandardCharsets.UTF_8);
                        }
                        res.put("ok", code >= 200 && code < 300);
                        res.put("status", code);
                        res.put("finalUrl", currentUrl);
                        res.put("body", responseText);
                        break;
                    }
                } catch (Exception e) {
                    try {
                        res.put("ok", false);
                        res.put("status", 0);
                        res.put("error", e.getMessage());
                    } catch (Exception ignored) {}
                } finally {
                    if (conn != null) conn.disconnect();
                }
                invokeDashboardCallback(cbId, res.toString());
            });
        }



        @JavascriptInterface
        public boolean hasNativeDownloadNotification() {
            return true;
        }

        @JavascriptInterface
        public void setExtractionActive(final boolean active, final String statusText) {
            mainHandler.post(() -> {
                try {
                    isExtractionActiveFlag = active;
                    mainHandler.removeCallbacks(bgExtractionHeartbeat);
                    if (active) {
                        ensureNotificationPermissionOnMainThread();
                        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
                        PowerManager pm = (PowerManager) getSystemService(Context.POWER_SERVICE);
                        if (pm != null) {
                            if (extractionWakeLock == null) {
                                extractionWakeLock = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "PocketLeads::ExtractionWakeLock");
                                extractionWakeLock.setReferenceCounted(false);
                            }
                            if (!extractionWakeLock.isHeld()) {
                                extractionWakeLock.acquire(4 * 60 * 60 * 1000L);
                            }
                        }
                        WifiManager wm = (WifiManager) getApplicationContext().getSystemService(Context.WIFI_SERVICE);
                        if (wm != null) {
                            if (extractionWifiLock == null) {
                                extractionWifiLock = wm.createWifiLock(WifiManager.WIFI_MODE_FULL_HIGH_PERF, "PocketLeads::ExtractionWifiLock");
                                extractionWifiLock.setReferenceCounted(false);
                            }
                            if (!extractionWifiLock.isHeld()) {
                                extractionWifiLock.acquire();
                            }
                        }
                        if (dashboardWebView != null) {
                            dashboardWebView.resumeTimers();
                        }
                        mainHandler.postDelayed(bgExtractionHeartbeat, 1500L);
                        showOngoingExtractionNotification(statusText != null && !statusText.isEmpty()
                                ? statusText
                                : "Extracting leads in background...");
                    } else {
                        getWindow().clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
                        if (extractionWakeLock != null && extractionWakeLock.isHeld()) {
                            extractionWakeLock.release();
                        }
                        if (extractionWifiLock != null && extractionWifiLock.isHeld()) {
                            extractionWifiLock.release();
                        }
                        cancelOngoingExtractionNotification();
                    }
                } catch (Exception ignored) {}
            });
        }

        @JavascriptInterface
        public void fetchRenderedWebsiteDomAsync(final String urlStr, final int waitMs, final String cbId) {
            mainHandler.post(() -> {
                if (!isSafeExternalScrapeUrl(urlStr, false)) {
                    invokeDashboardCallback(cbId, "{\"ok\":false,\"error\":\"Blocked unsafe URL\"}");
                    return;
                }
                final AtomicBoolean settled = new AtomicBoolean(false);
                final WebView ghost = new WebView(MainActivity.this);
                try {
                    WebSettings s = ghost.getSettings();
                    s.setJavaScriptEnabled(true);
                    s.setDomStorageEnabled(true);
                    s.setLoadsImagesAutomatically(false);
                    s.setBlockNetworkImage(true);
                    s.setUserAgentString(DESKTOP_USER_AGENT);
                    if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.LOLLIPOP) {
                        s.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW);
                    }
                    if (ghostWorkerContainer != null) {
                        ghostWorkerContainer.addView(ghost, new FrameLayout.LayoutParams(1, 1));
                    }
                    final Runnable cleanupAndExtract = () -> {
                        if (!settled.compareAndSet(false, true)) return;
                        try {
                            ghost.evaluateJavascript(
                                    "(function(){ try { var h = document.documentElement ? document.documentElement.outerHTML : ''; var t = document.body ? document.body.innerText : ''; return h + '\n' + t; } catch(e) { return ''; } })()",
                                    rawVal -> {
                                        try {
                                            String decoded = "";
                                            if (rawVal != null && rawVal.length() >= 2 && rawVal.startsWith("\"")) {
                                                decoded = new JSONArray("[" + rawVal + "]").optString(0, "");
                                            } else if (rawVal != null) {
                                                decoded = rawVal;
                                            }
                                            if (decoded.length() > 260000) {
                                                decoded = decoded.substring(0, 260000);
                                            }
                                            JSONObject out = new JSONObject();
                                            out.put("ok", !decoded.isEmpty());
                                            out.put("status", 200);
                                            out.put("finalUrl", urlStr);
                                            out.put("body", decoded);
                                            invokeDashboardCallback(cbId, out.toString());
                                        } catch (Exception ex) {
                                            invokeDashboardCallback(cbId, "{\"ok\":false,\"error\":\"Render parse failed\"}");
                                        } finally {
                                            try {
                                                ghost.stopLoading();
                                                if (ghostWorkerContainer != null) ghostWorkerContainer.removeView(ghost);
                                                ghost.destroy();
                                            } catch (Exception ignored) {}
                                        }
                                    }
                            );
                        } catch (Exception e) {
                            try {
                                if (ghostWorkerContainer != null) ghostWorkerContainer.removeView(ghost);
                                ghost.destroy();
                            } catch (Exception ignored) {}
                            invokeDashboardCallback(cbId, "{\"ok\":false,\"error\":\"Evaluate failed\"}");
                        }
                    };
                    final int renderDelay = Math.max(1400, Math.min(3800, waitMs > 0 ? waitMs : 2200));
                    ghost.setWebViewClient(new WebViewClient() {
                        @Override
                        public void onPageFinished(WebView view, String url) {
                            mainHandler.postDelayed(cleanupAndExtract, renderDelay);
                        }
                    });
                    mainHandler.postDelayed(cleanupAndExtract, renderDelay + 3200);
                    ghost.loadUrl(urlStr);
                } catch (Exception e) {
                    if (settled.compareAndSet(false, true)) {
                        try {
                            if (ghostWorkerContainer != null) ghostWorkerContainer.removeView(ghost);
                            ghost.destroy();
                        } catch (Exception ignored) {}
                        invokeDashboardCallback(cbId, "{\"ok\":false,\"error\":\"Ghost WebView error\"}");
                    }
                }
            });
        }

        @JavascriptInterface
        public void shareLastDownloadedFile() {
            ioPool.execute(() -> {
                try {
                    Uri shareUri = lastDownloadedUri;
                    String cleanName = (lastDownloadedName != null && !lastDownloadedName.isEmpty())
                            ? lastDownloadedName
                            : "PocketLeads_Export.csv";
                    String cleanMime = (lastDownloadedMime != null && !lastDownloadedMime.isEmpty())
                            ? lastDownloadedMime
                            : "text/csv";
                    if (lastDownloadedBytes != null && lastDownloadedBytes.length > 0) {
                        shareUri = writeBytesToShareCacheFile(cleanName, lastDownloadedBytes);
                    }
                    final Uri finalShareUri = shareUri;
                    final String finalMime = cleanMime;
                    final String finalName = cleanName;
                    mainHandler.post(() -> shareSavedUriWithPermission(finalShareUri, finalMime, finalName));
                } catch (Exception e) {
                    mainHandler.post(() -> Toast.makeText(
                            MainActivity.this,
                            "Share failed: " + e.getMessage(),
                            Toast.LENGTH_LONG
                    ).show());
                }
            });
        }

        @JavascriptInterface
        public void openLastDownloadedFile() {
            mainHandler.post(() -> openSavedUriWithPermission(lastDownloadedUri, lastDownloadedMime, lastDownloadedName));
        }

        @JavascriptInterface
        public void chooseFolderToSaveLastFile() {
            mainHandler.post(() -> launchChooseFolderSaveIntent(lastDownloadedName, lastDownloadedMime));
        }

        @JavascriptInterface
        public void chooseFolderToSaveFileDirect(final String filename, final String mimeType, final String base64Data) {
            ioPool.execute(() -> {
                try {
                    byte[] bytes = Base64.decode(base64Data, Base64.DEFAULT);
                    final String cleanName = (filename == null || filename.isEmpty())
                            ? ("PocketLeads_Export_" + System.currentTimeMillis() + ".csv")
                            : filename.replaceAll("[^a-zA-Z0-9._-]", "_");
                    final String cleanMime = (mimeType == null || mimeType.isEmpty()) ? "text/csv" : mimeType.split(";")[0];
                    lastDownloadedBytes = bytes;
                    lastDownloadedName = cleanName;
                    lastDownloadedMime = cleanMime;
                    Uri cacheUri = writeBytesToShareCacheFile(cleanName, bytes);
                    if (cacheUri != null) lastDownloadedUri = cacheUri;
                    mainHandler.post(() -> launchChooseFolderSaveIntent(cleanName, cleanMime));
                } catch (Exception e) {
                    mainHandler.post(() -> Toast.makeText(
                            MainActivity.this,
                            "Could not prepare file: " + e.getMessage(),
                            Toast.LENGTH_LONG
                    ).show());
                }
            });
        }

        @JavascriptInterface
        public void shareDownloadedFileDirect(final String filename, final String mimeType, final String base64Data) {
            ioPool.execute(() -> {
                try {
                    byte[] bytes = Base64.decode(base64Data, Base64.DEFAULT);
                    final String cleanName = (filename == null || filename.isEmpty())
                            ? ("PocketLeads_Export_" + System.currentTimeMillis() + ".csv")
                            : filename.replaceAll("[^a-zA-Z0-9._-]", "_");
                    final String cleanMime = (mimeType == null || mimeType.isEmpty()) ? "text/csv" : mimeType.split(";")[0];
                    lastDownloadedBytes = bytes;
                    lastDownloadedMime = cleanMime;
                    lastDownloadedName = cleanName;
                    Uri shareUri = writeBytesToShareCacheFile(cleanName, bytes);
                    try {
                        Uri mediaUri = writeBytesToDownloadsMediaStore(cleanName, cleanMime, bytes);
                        if (shareUri == null) shareUri = mediaUri;
                    } catch (Exception ignored) {}
                    lastDownloadedUri = shareUri;
                    final Uri finalShareUri = shareUri;
                    mainHandler.post(() -> shareSavedUriWithPermission(finalShareUri, cleanMime, cleanName));
                } catch (Exception e) {
                    mainHandler.post(() -> Toast.makeText(
                            MainActivity.this,
                            "Share failed: " + e.getMessage(),
                            Toast.LENGTH_LONG
                    ).show());
                }
            });
        }

        @JavascriptInterface
        public void saveDownloadedFile(final String filename, final String mimeType, final String base64Data) {
            ioPool.execute(() -> {
                try {
                    byte[] bytes = Base64.decode(base64Data, Base64.DEFAULT);
                    final String cleanName = (filename == null || filename.isEmpty())
                            ? ("PocketLeads_Export_" + System.currentTimeMillis() + ".csv")
                            : filename.replaceAll("[^a-zA-Z0-9._-]", "_");
                    final String cleanMime = (mimeType == null || mimeType.isEmpty()) ? "text/csv" : mimeType.split(";")[0];
                    lastDownloadedBytes = bytes;
                    lastDownloadedMime = cleanMime;
                    lastDownloadedName = cleanName;

                    // 1. Always write a shareable copy to ShareFileProvider cache AND MediaStore.Downloads
                    //    so Share and Open work immediately even before or if user cancels the folder picker.
                    Uri shareCacheUri = writeBytesToShareCacheFile(cleanName, bytes);
                    Uri savedUri = null;
                    try {
                        savedUri = writeBytesToDownloadsMediaStore(cleanName, cleanMime, bytes);
                    } catch (Exception ignored) {}
                    lastDownloadedUri = (shareCacheUri != null) ? shareCacheUri : savedUri;

                    // 2. Notify user & post download completed notification (folder picker is triggered explicitly via Save As!)
                    mainHandler.post(() -> {
                        Toast.makeText(MainActivity.this, "✓ Saved in Downloads/" + cleanName, Toast.LENGTH_SHORT).show();
                        postDownloadCompletedNotification(lastDownloadedUri, cleanName, cleanMime, bytes.length);
                    });
                } catch (Exception e) {
                    mainHandler.post(() -> Toast.makeText(
                            MainActivity.this,
                            "Export failed: " + e.getMessage(),
                            Toast.LENGTH_LONG
                    ).show());
                }
            });
        }

        @JavascriptInterface
        public void cancelAllNotifications() {
            mainHandler.post(() -> {
                try {
                    NotificationManager nm = (NotificationManager) getSystemService(Context.NOTIFICATION_SERVICE);
                    if (nm != null) {
                        nm.cancel(7701);
                        nm.cancelAll();
                    }
                } catch (Exception ignored) {}
            });
        }

        @JavascriptInterface
        public void pickGoogleAccountAsync(final String cbId) {
            mainHandler.post(() -> {
                try {
                    pendingGoogleAccountCallbackId = cbId;
                    Intent intent;
                    if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                        intent = android.accounts.AccountManager.newChooseAccountIntent(
                                null, null, new String[]{"com.google"}, null, null, null, null
                        );
                    } else {
                        intent = android.accounts.AccountManager.newChooseAccountIntent(
                                null, null, new String[]{"com.google"}, false, null, null, null, null
                        );
                    }
                    startActivityForResult(intent, GOOGLE_ACCOUNT_PICKER_RESULT_CODE);
                } catch (Exception e) {
                    pendingGoogleAccountCallbackId = null;
                    invokeDashboardCallback(cbId, "{\"ok\":false,\"error\":\"Account picker unavailable\"}");
                }
            });
        }

        @JavascriptInterface
        public void showNotification(final String id, final String title, final String message) {
            mainHandler.post(() -> {
                try {
                    ensureNotificationPermissionOnMainThread();
                    String cleanId = (id != null && !id.isEmpty()) ? id : "pocketleads_scrape_status";
                    String channelId = "pocketleads_alerts_v2";
                    NotificationManager nm = (NotificationManager) getSystemService(Context.NOTIFICATION_SERVICE);
                    if (nm != null) {
                        Intent clickIntent = new Intent(MainActivity.this, MainActivity.class);
                        clickIntent.setAction("com.pocketleads.pro.NOTIF_CLICK_" + cleanId + "_" + System.currentTimeMillis());
                        clickIntent.putExtra("pl_notification_clicked", true);
                        clickIntent.putExtra("pl_notification_id", cleanId);
                        clickIntent.putExtra("pl_notification_title", title != null ? title : "");
                        clickIntent.putExtra("pl_notification_message", message != null ? message : "");
                        clickIntent.addFlags(Intent.FLAG_ACTIVITY_SINGLE_TOP | Intent.FLAG_ACTIVITY_CLEAR_TOP);

                        int pendingFlags = PendingIntent.FLAG_UPDATE_CURRENT;
                        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                            pendingFlags |= PendingIntent.FLAG_IMMUTABLE;
                        }
                        PendingIntent contentIntent = PendingIntent.getActivity(
                                MainActivity.this,
                                cleanId.hashCode(),
                                clickIntent,
                                pendingFlags
                        );

                        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                            NotificationChannel channel = new NotificationChannel(
                                    channelId,
                                    "PocketLeads Alerts",
                                    NotificationManager.IMPORTANCE_HIGH
                            );
                            nm.createNotificationChannel(channel);
                            Notification notif = new Notification.Builder(MainActivity.this, channelId)
                                    .setContentTitle(title)
                                    .setContentText(message)
                                    .setSmallIcon(R.mipmap.ic_launcher)
                                    .setContentIntent(contentIntent)
                                    .setAutoCancel(true)
                                    .build();
                            nm.notify(cleanId.hashCode(), notif);
                        } else {
                            Notification notif = new Notification.Builder(MainActivity.this)
                                    .setContentTitle(title)
                                    .setContentText(message)
                                    .setSmallIcon(R.mipmap.ic_launcher)
                                    .setContentIntent(contentIntent)
                                    .setAutoCancel(true)
                                    .build();
                            nm.notify(cleanId.hashCode(), notif);
                        }
                    }
                } catch (Exception ignored) {}
            });
        }
    }

    private void postDownloadCompletedNotification(Uri fileUri, String cleanName, String cleanMime, int byteLen) {
        try {
            NotificationManager nm = (NotificationManager) getSystemService(Context.NOTIFICATION_SERVICE);
            if (nm == null) return;
            String dlChannelId = "pocketleads_downloads_v2";
            Intent openClickIntent = new Intent(MainActivity.this, MainActivity.class);
            openClickIntent.setAction("com.pocketleads.pro.OPEN_DL_" + System.currentTimeMillis());
            openClickIntent.putExtra("pl_open_downloaded_file", true);
            openClickIntent.putExtra("pl_file_uri", fileUri != null ? fileUri.toString() : "");
            openClickIntent.putExtra("pl_file_mime", cleanMime);
            openClickIntent.putExtra("pl_file_name", cleanName);
            openClickIntent.addFlags(Intent.FLAG_ACTIVITY_SINGLE_TOP | Intent.FLAG_ACTIVITY_CLEAR_TOP);
            int pFlags = PendingIntent.FLAG_UPDATE_CURRENT;
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                pFlags |= PendingIntent.FLAG_IMMUTABLE;
            }
            PendingIntent pi = PendingIntent.getActivity(
                    MainActivity.this,
                    ("dl_" + cleanName).hashCode(),
                    openClickIntent,
                    pFlags
            );
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                NotificationChannel ch = new NotificationChannel(
                        dlChannelId,
                        "PocketLeads Downloads",
                        NotificationManager.IMPORTANCE_HIGH
                );
                nm.createNotificationChannel(ch);
                String sizeText = String.format(java.util.Locale.US, "%.1f KB", Math.max(0.1, byteLen / 1024.0));
                Notification notif = new Notification.Builder(MainActivity.this, dlChannelId)
                        .setContentTitle(cleanName)
                        .setContentText(sizeText + " • Saved • Tap to open")
                        .setSmallIcon(android.R.drawable.stat_sys_download_done)
                        .setContentIntent(pi)
                        .addAction(new Notification.Action.Builder(0, "Open", pi).build())
                        .setAutoCancel(true)
                        .build();
                nm.notify(("dl_" + cleanName).hashCode(), notif);
            } else {
                Notification notif = new Notification.Builder(MainActivity.this)
                        .setContentTitle("⬇ Download Complete: " + cleanName)
                        .setContentText("Saved • Tap to open file")
                        .setSmallIcon(android.R.drawable.stat_sys_download_done)
                        .setContentIntent(pi)
                        .setAutoCancel(true)
                        .build();
                nm.notify(("dl_" + cleanName).hashCode(), notif);
            }
        } catch (Exception ignored) {}
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        if (requestCode == FILE_CHOOSER_RESULT_CODE) {
            if (filePathCallback == null) return;
            Uri[] results = WebChromeClient.FileChooserParams.parseResult(resultCode, data);
            filePathCallback.onReceiveValue(results);
            filePathCallback = null;
        } else if (requestCode == CREATE_DOC_RESULT_CODE) {
            if (resultCode == Activity.RESULT_OK && data != null && data.getData() != null && lastDownloadedBytes != null) {
                final Uri destUri = data.getData();
                final byte[] bytesToCopy = lastDownloadedBytes;
                final String savedName = lastDownloadedName != null ? lastDownloadedName : "PocketLeads_Export";
                final String savedMime = lastDownloadedMime != null ? lastDownloadedMime : "application/octet-stream";
                ioPool.execute(() -> {
                    try (OutputStream os = getContentResolver().openOutputStream(destUri)) {
                        if (os != null) {
                            os.write(bytesToCopy);
                            os.flush();
                        }
                        mainHandler.post(() -> {
                            postDownloadCompletedNotification(destUri, savedName, savedMime, bytesToCopy.length);
                            Toast.makeText(
                                    MainActivity.this,
                                    "✓ File saved to selected folder: " + savedName,
                                    Toast.LENGTH_LONG
                            ).show();
                        });
                    } catch (Exception e) {
                        mainHandler.post(() -> Toast.makeText(
                                MainActivity.this,
                                "Could not write to folder: " + e.getMessage(),
                                Toast.LENGTH_LONG
                        ).show());
                    }
                });
            }
        } else if (requestCode == GOOGLE_ACCOUNT_PICKER_RESULT_CODE) {
            final String cbId = pendingGoogleAccountCallbackId;
            pendingGoogleAccountCallbackId = null;
            if (cbId != null) {
                try {
                    JSONObject out = new JSONObject();
                    if (resultCode == Activity.RESULT_OK && data != null) {
                        String accName = data.getStringExtra(android.accounts.AccountManager.KEY_ACCOUNT_NAME);
                        if (accName != null && !accName.trim().isEmpty()) {
                            out.put("ok", true);
                            out.put("email", accName.trim().toLowerCase());
                            invokeDashboardCallback(cbId, out.toString());
                            return;
                        }
                    }
                    out.put("ok", false);
                    out.put("cancelled", resultCode == Activity.RESULT_CANCELED);
                    invokeDashboardCallback(cbId, out.toString());
                } catch (Exception e) {
                    invokeDashboardCallback(cbId, "{\"ok\":false}");
                }
            }
        } else {
            super.onActivityResult(requestCode, resultCode, data);
        }
    }

    private Uri writeBytesToShareCacheFile(String cleanName, byte[] bytes) {
        try {
            File shareDir = new File(getCacheDir(), "shared_exports");
            if (!shareDir.exists()) shareDir.mkdirs();
            // Clean up old cached files (> 12 files) so cache stays tiny
            File[] existing = shareDir.listFiles();
            if (existing != null && existing.length > 12) {
                for (File old : existing) {
                    if (!old.getName().equals(cleanName)) {
                        try { old.delete(); } catch (Exception ignored) {}
                    }
                }
            }
            File outFile = new File(shareDir, cleanName);
            try (FileOutputStream fos = new FileOutputStream(outFile, false)) {
                fos.write(bytes);
                fos.flush();
            }
            return ShareFileProvider.getUriForFile(outFile);
        } catch (Exception e) {
            return null;
        }
    }

    private Uri writeBytesToDownloadsMediaStore(String cleanName, String cleanMime, byte[] bytes) throws Exception {
        Uri savedUri = null;
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
            ContentValues values = new ContentValues();
            values.put(MediaStore.Downloads.DISPLAY_NAME, cleanName);
            values.put(MediaStore.Downloads.MIME_TYPE, cleanMime);
            values.put(MediaStore.Downloads.RELATIVE_PATH, Environment.DIRECTORY_DOWNLOADS);
            savedUri = getContentResolver().insert(MediaStore.Downloads.EXTERNAL_CONTENT_URI, values);
            if (savedUri != null) {
                try (OutputStream os = getContentResolver().openOutputStream(savedUri)) {
                    if (os != null) {
                        os.write(bytes);
                        os.flush();
                    }
                }
            }
        } else {
            File dir = Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DOWNLOADS);
            if (!dir.exists()) dir.mkdirs();
            File outFile = new File(dir, cleanName);
            try (FileOutputStream fos = new FileOutputStream(outFile)) {
                fos.write(bytes);
                fos.flush();
            }
        }
        return savedUri;
    }

    private void launchChooseFolderSaveIntent(String fileName, String mimeType) {
        if (lastDownloadedBytes == null || lastDownloadedBytes.length == 0) {
            Toast.makeText(this, "Please download or export a file first.", Toast.LENGTH_SHORT).show();
            return;
        }
        String safeName = (fileName != null && !fileName.isEmpty()) ? fileName : "PocketLeads_Export.xlsx";
        String safeMime = (mimeType != null && !mimeType.isEmpty()) ? mimeType : "*/*";
        try {
            Intent intent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
            intent.addCategory(Intent.CATEGORY_OPENABLE);
            intent.setType(safeMime);
            intent.putExtra(Intent.EXTRA_TITLE, safeName);
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O && Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
                try {
                    intent.putExtra("android.provider.extra.INITIAL_URI", MediaStore.Downloads.EXTERNAL_CONTENT_URI);
                } catch (Exception ignored) {}
            }
            startActivityForResult(intent, CREATE_DOC_RESULT_CODE);
        } catch (Exception firstErr) {
            try {
                Intent fallbackIntent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
                fallbackIntent.addCategory(Intent.CATEGORY_OPENABLE);
                fallbackIntent.setType("*/*");
                fallbackIntent.putExtra(Intent.EXTRA_TITLE, safeName);
                startActivityForResult(fallbackIntent, CREATE_DOC_RESULT_CODE);
            } catch (Exception e) {
                Toast.makeText(this, "✓ Saved in Downloads/" + safeName, Toast.LENGTH_LONG).show();
            }
        }
    }

    private void ensureNotificationPermissionOnMainThread() {
        try {
            if (Build.VERSION.SDK_INT >= 33 && !notifPermRequested) {
                if (checkSelfPermission("android.permission.POST_NOTIFICATIONS") != PackageManager.PERMISSION_GRANTED) {
                    notifPermRequested = true;
                    requestPermissions(new String[]{"android.permission.POST_NOTIFICATIONS"}, 5109);
                }
            }
        } catch (Exception ignored) {}
    }

    private void showOngoingExtractionNotification(String statusText) {
        try {
            NotificationManager nm = (NotificationManager) getSystemService(Context.NOTIFICATION_SERVICE);
            if (nm == null) return;
            String channelId = "pocketleads_bg_keepalive_v1";
            Intent clickIntent = new Intent(MainActivity.this, MainActivity.class);
            clickIntent.addFlags(Intent.FLAG_ACTIVITY_SINGLE_TOP | Intent.FLAG_ACTIVITY_CLEAR_TOP);
            int pendingFlags = PendingIntent.FLAG_UPDATE_CURRENT;
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                pendingFlags |= PendingIntent.FLAG_IMMUTABLE;
            }
            PendingIntent contentIntent = PendingIntent.getActivity(this, 7701, clickIntent, pendingFlags);
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                NotificationChannel channel = new NotificationChannel(
                        channelId,
                        "PocketLeads Background Service",
                        NotificationManager.IMPORTANCE_LOW
                );
                channel.setDescription("Keeps lead & email extraction active while screen is off or minimized");
                nm.createNotificationChannel(channel);
                Notification notif = new Notification.Builder(this, channelId)
                        .setContentTitle("⚡ PocketLeads PRO Active")
                        .setContentText(statusText)
                        .setSmallIcon(R.mipmap.ic_launcher)
                        .setContentIntent(contentIntent)
                        .setOngoing(false)
                        .setAutoCancel(true)
                        .build();
                nm.notify(7701, notif);
            } else {
                Notification notif = new Notification.Builder(this)
                        .setContentTitle("⚡ PocketLeads PRO Active")
                        .setContentText(statusText)
                        .setSmallIcon(R.mipmap.ic_launcher)
                        .setContentIntent(contentIntent)
                        .setOngoing(false)
                        .setAutoCancel(true)
                        .build();
                nm.notify(7701, notif);
            }
        } catch (Exception ignored) {}
    }

    private void cancelOngoingExtractionNotification() {
        try {
            NotificationManager nm = (NotificationManager) getSystemService(Context.NOTIFICATION_SERVICE);
            if (nm != null) nm.cancel(7701);
        } catch (Exception ignored) {}
    }

    @Override
    public void onBackPressed() {
        if (waOverlayContainer != null && waOverlayContainer.getVisibility() == View.VISIBLE) {
            waOverlayContainer.setVisibility(View.GONE);
            return;
        }
        if (dashboardWebView != null) {
            dashboardWebView.evaluateJavascript(
                    "(function(){ try { return (typeof window.__handleAndroidBackButton === 'function') ? window.__handleAndroidBackButton() : 'exit'; } catch(e) { return 'exit'; } })()",
                    value -> {
                        if (value != null && value.contains("handled")) {
                            return;
                        }
                        long now = System.currentTimeMillis();
                        if (now - lastBackPressMs < 2200L) {
                            lastBackPressMs = 0L;
                            moveTaskToBack(true);
                        } else {
                            lastBackPressMs = now;
                            Toast.makeText(MainActivity.this, "Press Back again to minimize PocketLeads", Toast.LENGTH_SHORT).show();
                        }
                    }
            );
            return;
        }
        moveTaskToBack(true);
    }

    private void shareSavedUriWithPermission(Uri uri, String mimeType, String displayName) {
        String safeName = (displayName != null && !displayName.isEmpty())
                ? displayName
                : (lastDownloadedName != null && !lastDownloadedName.isEmpty() ? lastDownloadedName : "PocketLeads_Export.csv");
        String cleanMime = (mimeType != null && !mimeType.isEmpty())
                ? mimeType.split(";")[0]
                : (lastDownloadedMime != null && !lastDownloadedMime.isEmpty() ? lastDownloadedMime : "text/csv");

        Uri shareUri = uri;
        if (lastDownloadedBytes != null && lastDownloadedBytes.length > 0) {
            Uri providerUri = writeBytesToShareCacheFile(safeName, lastDownloadedBytes);
            if (providerUri != null) {
                shareUri = providerUri;
            }
        }
        if (shareUri == null) {
            Toast.makeText(this, "Please export a file first to share.", Toast.LENGTH_SHORT).show();
            return;
        }
        try {
            Intent shareIntent = new Intent(Intent.ACTION_SEND);
            shareIntent.setType(cleanMime);
            shareIntent.putExtra(Intent.EXTRA_STREAM, shareUri);
            shareIntent.putExtra(Intent.EXTRA_TITLE, safeName);
            shareIntent.putExtra(Intent.EXTRA_SUBJECT, safeName);
            try {
                android.content.ClipData clip = android.content.ClipData.newRawUri(safeName, shareUri);
                shareIntent.setClipData(clip);
            } catch (Exception ignored) {}
            shareIntent.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION);

            try {
                List<android.content.pm.ResolveInfo> resInfoList = getPackageManager().queryIntentActivities(shareIntent, PackageManager.MATCH_DEFAULT_ONLY);
                for (android.content.pm.ResolveInfo resolveInfo : resInfoList) {
                    if (resolveInfo != null && resolveInfo.activityInfo != null && resolveInfo.activityInfo.packageName != null) {
                        grantUriPermission(resolveInfo.activityInfo.packageName, shareUri, Intent.FLAG_GRANT_READ_URI_PERMISSION);
                    }
                }
            } catch (Exception ignored) {}

            Intent chooser = Intent.createChooser(shareIntent, null);
            chooser.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION);
            startActivity(chooser);
        } catch (Exception e) {
            Toast.makeText(this, "Share error: " + e.getMessage(), Toast.LENGTH_LONG).show();
        }
    }

    private void openSavedUriWithPermission(Uri uri, String mimeType, String fileName) {
        try {
            if (uri != null) {
                String safeMime = (mimeType != null && !mimeType.isEmpty())
                        ? mimeType
                        : "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet";
                Intent openIntent = new Intent(Intent.ACTION_VIEW);
                openIntent.setDataAndType(uri, safeMime);
                openIntent.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION | Intent.FLAG_ACTIVITY_NEW_TASK);
                try {
                    List<android.content.pm.ResolveInfo> resInfoList = getPackageManager().queryIntentActivities(openIntent, PackageManager.MATCH_DEFAULT_ONLY);
                    for (android.content.pm.ResolveInfo resolveInfo : resInfoList) {
                        String pkg = resolveInfo.activityInfo.packageName;
                        grantUriPermission(pkg, uri, Intent.FLAG_GRANT_READ_URI_PERMISSION);
                    }
                } catch (Exception ignored) {}
                Intent chooser = Intent.createChooser(openIntent, "Open " + (fileName != null ? fileName : "File"));
                chooser.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_GRANT_READ_URI_PERMISSION);
                startActivity(chooser);
                return;
            }
        } catch (Exception ignored) {}
        try {
            Intent dlIntent = new Intent(android.app.DownloadManager.ACTION_VIEW_DOWNLOADS);
            dlIntent.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
            startActivity(dlIntent);
        } catch (Exception ignored) {}
    }

    private int dpToPx(int dp) {
        float density = getResources().getDisplayMetrics().density;
        return Math.round(dp * density);
    }
}
