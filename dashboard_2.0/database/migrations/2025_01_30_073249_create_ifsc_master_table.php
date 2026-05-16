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

        if (!Schema::hasTable('ifsc_master')) {
            Schema::create('ifsc_master', function (Blueprint $table) {
                $table->id('bank_id');
                $table->string('bank_name')->nullable();
                $table->string('ifsc_code')->nullable();
                $table->string('bank_branch')->nullable();
                $table->text('address')->nullable();
                $table->text('district')->nullable();
                $table->string('bank_city')->nullable();
                $table->text('state')->nullable();
                $table->text('phone')->nullable();
                $table->string('std_code')->nullable();
            });
        }
    }
    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('ifsc_master');
    }
};
