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
        Schema::table('MenuMaster', function (Blueprint $table) {
            //
            $table->enum('isFrontEnd',['Y','N'])->default('N')->comment('menu to send in response to frontend only ');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('MenuMaster', function (Blueprint $table) {
            //
            $table->dropColumn('isFrontEnd');
        });
    }
};
