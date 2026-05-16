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
        Schema::table('oem_masters', function (Blueprint $table) {
            $table->string('misp_code')->nullable();
            $table->string('pin_code')->nullable();
            $table->string('city')->nullable();
            $table->string('state')->nullable();
            $table->string('mob_no')->nullable();
            $table->string('email')->nullable();
            $table->enum('status',['Y','N'])->default('Y');
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('oem_masters', function (Blueprint $table) {
            //
        });
    }
};
