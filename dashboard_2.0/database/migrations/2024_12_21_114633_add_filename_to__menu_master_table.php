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
        if (!Schema::hasTable('MenuMaster')) {
            Schema::table('MenuMaster', function (Blueprint $table) {
                $table->string('filename')->nullable()->after('order_by');
            }); 
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('MenuMaster');
    }
};
