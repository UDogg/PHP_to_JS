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
        Schema::create('misp_branches', function (Blueprint $table) {
            $table->id('branch_id');
            $table->string('oem_id')->nullable();
            $table->string('oem_name')->nullable();
            $table->string('misp_id')->nullable();
            $table->string('misp_name')->nullable();
            $table->string('branch_name')->nullable();
            $table->string('address')->nullable();
            $table->string('city')->nullable();
            $table->string('state')->nullable();
            $table->string('pin_code')->nullable();
            $table->string('code')->nullable();

            $table->timestamps();
        });
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('misp_branches');
    }
};
