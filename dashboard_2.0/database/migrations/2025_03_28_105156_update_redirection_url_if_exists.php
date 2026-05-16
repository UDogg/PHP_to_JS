<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if (Schema::hasTable('cta_master') && Schema::hasColumn('cta_master', 'redirection_url')) {
            Schema::table('cta_master', function (Blueprint $table) {
                $table->string('redirection_url')->nullable()->change(); 
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        if (Schema::hasTable('cta_master') && Schema::hasColumn('cta_master', 'redirection_url')) {
            Schema::table('cta_master', function (Blueprint $table) {
                $table->string('redirection_url')->nullable()->change(); 
            });
        }
    }
};
