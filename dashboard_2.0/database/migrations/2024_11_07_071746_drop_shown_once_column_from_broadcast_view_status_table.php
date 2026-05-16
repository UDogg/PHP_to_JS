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
        Schema::table('broadcast_view_status', function (Blueprint $table) {
            $table->dropColumn('shown_once'); 
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('broadcast_view_status', function (Blueprint $table) {
            $table->boolean('shown_once')->default(false); 
        });
    }
};
